-- Prove2me | Theorems.Thm_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_of_liesOverPrime_xHTop
-- name    : ModularCurve.exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_of_liesOverPrime_xHTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/9ecf0c6d-9bce-5725-bf8d-f1170dc7aa69
-- title:
--   Gauss reduction at a place over p intertwining α and β
-- statement:
--   Let $p$ and $\ell$ be primes with $p \neq \ell$, let $N \geq 1$ with $p \nmid N$ (no condition relating $\ell$ and $N$ is imposed), and let $H' \leq (\mathbb{Z}/N)^\times$. Assume `HeckeBetaHDefined N H' ℓ`, i.e. $q \mapsto q^{\ell}$ (the map `qExpand ℚ ℓ` on Laurent series) carries `xHFunctionField N H'` into `xHTopFunctionFieldC ℚ N H' (N*ℓ)`, the $q$-expansion field of $\Gamma_{H'}(N) \cap \Gamma_0(N\ell)$ over $\mathbb{Q}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that $p$ is a non-unit of $A$, with residue field $\kappa$, and assume the corresponding statement `HeckeBetaModLHDefined` over $\kappa$: `qExpand κ ℓ` carries `qExpFunctionFieldC κ (CohCarrier.GammaH N H')` into `qExpFunctionFieldC κ (CohCarrier.GammaH N H' ⊓ Gamma0 (N*ℓ))`. Let $W$ be a valuation subring of $\overline{\mathbb{Q}} \cdot F(\Gamma_{H'}(N))$ — the field `xHFunctionFieldBar N H'`, the base change of `xHFunctionField N H'` to $\overline{\mathbb{Q}}$ inside Laurent series — and $W'$ a valuation subring of the base change to $\overline{\mathbb{Q}}$ of `xHTopFunctionFieldC ℚ N H' (N*ℓ)`, each characterised by the same $A$-integral Gauss presentation: $f$ belongs to the ring precisely when there are power series $x, y \in A[[q]]$ with $y$ having nonzero reduction in $\kappa[[q]]$ and $f \cdot y = x$ as Laurent series over $\overline{\mathbb{Q}}$. The conclusion asserts the existence of ring homomorphisms $\mathrm{red} : W \to$ `qExpFunctionFieldC κ (CohCarrier.GammaH N H')` and $\mathrm{red}' : W' \to$ `qExpFunctionFieldC κ (CohCarrier.GammaH N H' ⊓ Gamma0 (N*ℓ))` such that: each is computed on presentations, namely whenever $f \cdot y = x$ with $x, y \in A[[q]]$ and $y$ of nonzero reduction, the image satisfies $\mathrm{red}(f) \cdot \bar{y} = \bar{x}$ over $\kappa$ (and likewise for $\mathrm{red}'$); both are surjective; the kernel of each is the maximal ideal of $W$, respectively $W'$; and for every $f \in W$ the element `heckeAlphaHBar` $f$ (the inclusion into the level-$N\ell$ field) lies in $W'$ with $\mathrm{red}'$ of it equal to `heckeAlphaModLH` applied to $\mathrm{red}(f)$, and similarly `heckeBetaHBar` $f$ lies in $W'$ with $\mathrm{red}'$ of it equal to `heckeBetaModLH` applied to $\mathrm{red}(f)$, where under the two hypotheses above $\beta$ is on both sides the map $q \mapsto q^{\ell}$.
--
--   This is the good-reduction comparison for modular function fields in the style of Igusa: the Gauss valuation ring at a place of $\overline{\mathbb{Q}}$ above $p \nmid N$ reduces the characteristic-zero function fields of $X_{H'}(N)$ and of the level-$N\ell$ roof onto the corresponding $q$-expansion fields in characteristic $p$, with kernels the maximal ideals and compatibly with the degeneracy map $\alpha$ and the $q \mapsto q^{\ell}$ map $\beta$. It feeds the construction of the pair of isomorphisms of characteristic-$p$ $q$-expansion fields intertwining $\alpha$, $\beta$ and reduction of the Fricke involution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_of_liesOverPrime_xHTop.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_of_liesOverPrime_xHTop
    (p N : ℕ) [Fact p.Prime] [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hpN : ¬ p ∣ N) (hpℓ : p ≠ ℓ)
    (hβ0 : ModularCurve.HeckeBetaHDefined N H' ℓ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hβ : ModularCurve.HeckeBetaModLHDefined (IsLocalRing.ResidueField ↥A) N H' ℓ)
    (W : ValuationSubring ↥(xHFunctionFieldBar N H'))
    (hW : ∀ f : ↥(xHFunctionFieldBar N H'), f ∈ W ↔ ∃ x y : PowerSeries ↥A, y.map (IsLocalRing.residue ↥A) ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ))))
    (W' : ValuationSubring ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ N H' (N * ℓ))))
    (hW' : ∀ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ N H' (N * ℓ))), f ∈ W' ↔ ∃ x y : PowerSeries ↥A, y.map (IsLocalRing.residue ↥A) ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ)))) :
    ∃ (red : ↥W →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H')))
      (red' : ↥W' →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))),

      (∀ (f : ↥W) (x y : PowerSeries ↥A), y.map (IsLocalRing.residue ↥A) ≠ 0 →
        ((f : ↥(xHFunctionFieldBar N H')) : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ))) →
        ((red f : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H'))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) *
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥A) (y.map (IsLocalRing.residue ↥A)) =
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥A) (x.map (IsLocalRing.residue ↥A))) ∧
      (∀ (f : ↥W') (x y : PowerSeries ↥A), y.map (IsLocalRing.residue ↥A) ≠ 0 →
        ((f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ N H' (N * ℓ)))) : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ))) →
        ((red' f : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) *
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥A) (y.map (IsLocalRing.residue ↥A)) =
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField ↥A) (x.map (IsLocalRing.residue ↥A))) ∧

      Function.Surjective red ∧ Function.Surjective red' ∧
      RingHom.ker red = IsLocalRing.maximalIdeal ↥W ∧ RingHom.ker red' = IsLocalRing.maximalIdeal ↥W' ∧

      (∀ f : ↥W, ∃ h : heckeAlphaHBar (AlgebraicClosure ℚ) N H' ℓ (f : ↥(xHFunctionFieldBar N H')) ∈ W',
        red' ⟨_, h⟩ = ModularCurve.heckeAlphaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ (red f)) ∧

      (∀ f : ↥W, ∃ h : heckeBetaHBar (AlgebraicClosure ℚ) N H' ℓ (f : ↥(xHFunctionFieldBar N H')) ∈ W',
        red' ⟨_, h⟩ = ModularCurve.heckeBetaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ (red f)) := by sorry
