-- Prove2me | Theorems.Thm_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop
-- name    : ModularCurve.exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/05835337-7d09-59d5-a8ce-9fc8fa04e40e
-- title:
--   Gauss reduction onto the mod-p q-expansion fields
-- statement:
--   Let $p$ and $\ell$ be primes with $p \neq \ell$, let $N \geq 1$ with $p \nmid N$ and $\ell \nmid N$, and let $H' \leq (\mathbb{Z}/N)^\times$. Assume `HeckeBetaHDefined N H' ℓ`, i.e. $\mathrm{qExpand}_{\mathbb{Q},\ell}$ carries the function field $F(\Gamma_{H'}(N))$ into $F(\Gamma_{H'}(N) \cap \Gamma_0(N\ell))$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, and write $\kappa = \mathrm{ResidueField}(A)$; assume the corresponding statement `HeckeBetaModLHDefined` over $\kappa$, that $\mathrm{qExpand}_{\kappa,\ell}$ maps the $q$-expansion field $F_\kappa$ of $\Gamma_{H'}(N)$ into that of $\Gamma_{H'}(N) \cap \Gamma_0(N\ell)$. Let $\rho$ be a homomorphism from $\Gamma_0(N)$ to the $\kappa$-algebra automorphisms of $F_\kappa$ satisfying `IsDiamondPullbackModL`: whenever $f, g, f_1, g_1$ are modular forms of weight $k$ on $\Gamma_{H'}(N)$ with integral $q$-expansions $p_f, p_g, p_{f_1}, p_{g_1}$, $f_1 = f\mid_k \gamma$, $g_1 = g\mid_k \gamma$, the reduction of $p_g$ over $\kappa$ is nonzero, and $x \in F_\kappa$ has Laurent expansion $\bar{p}_{f_1}/\bar{p}_{g_1}$, then $\rho(\gamma)x$ has expansion $\bar{p}_f/\bar{p}_g$. Finally let $W$ and $W'$ be valuation subrings of $\bar F = \overline{\mathbb{Q}} \cdot F(\Gamma_{H'}(N))$ and of $\bar F' = \overline{\mathbb{Q}} \cdot F(\Gamma_{H'}(N) \cap \Gamma_0(N\ell))$ inside $\overline{\mathbb{Q}}((q))$, consisting exactly of those $f$ admitting a presentation $f \cdot y = x$ with $x, y$ power series over $A$ whose reduction $\bar y$ is nonzero (the Gauss points). The assertion is that there exist ring homomorphisms $\mathrm{red} \colon W \to F_\kappa$ and $\mathrm{red}' \colon W' \to F'_\kappa$ such that: each is computed on presentations, i.e. $f \cdot y = x$ as above forces $\mathrm{red}(f) \cdot \bar y = \bar x$ in $\kappa((q))$, and likewise for $\mathrm{red}'$; both are surjective with kernels the maximal ideals of $W$ and $W'$; for every $f \in W$ the image of $f$ under the inclusion $\mathrm{heckeAlphaHBar}$ lies in $W'$ and $\mathrm{red}'$ of it equals $\mathrm{heckeAlphaModLH}(\mathrm{red}(f))$, the inclusion $F_\kappa \hookrightarrow F'_\kappa$; the same compatibility holds for $\mathrm{heckeBetaHBar}$ and $\mathrm{heckeBetaModLH}$, the maps given by $\mathrm{qExpand}_\ell$ under the two hypotheses above; and for every $\gamma \in \Gamma_0(N)$ and $d \in (\mathbb{Z}/N)^\times$ with the lower-right entry of $\gamma$ congruent to $d$ modulo $N$, and every $x \in F_\kappa$, there is $f \in W$ with $\mathrm{diamondAutHBar}_{N,H'}(d)(f) \in W$, $\mathrm{red}(f) = x$ and $\mathrm{red}(\mathrm{diamondAutHBar}_{N,H'}(d)(f)) = \rho(\gamma)x$ (a simultaneously compatible lift).
--
--   This is the good-reduction statement of Deuring–Igusa type for the modular curves $X_{H'}(N)$ and $X_{H'}(N) \cap \Gamma_0(N\ell)$ at a prime $p \nmid N\ell$, in the form that the residue field of the Gauss point of the function field is the characteristic-$p$ $q$-expansion field, compatibly with the two degeneracy maps $\alpha, \beta$ and with the diamond operators. It is used in the construction of the mod-$\ell$ diamond action and of the identification of $\beta$ with $\alpha$ in characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop.lean

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

theorem ModularCurve.exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_diamondLift_of_liesOverPrime_xHTop
    (p N : ℕ) [Fact p.Prime] [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hpN : ¬ p ∣ N) (hpℓ : p ≠ ℓ) (hℓN : ¬ ℓ ∣ N)
    (hβ0 : ModularCurve.HeckeBetaHDefined N H' ℓ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hβ : ModularCurve.HeckeBetaModLHDefined (IsLocalRing.ResidueField ↥A) N H' ℓ)
    (ρ : CongruenceSubgroup.Gamma0 N →*
        (↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H')) ≃ₐ[IsLocalRing.ResidueField ↥A]
          ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H'))))
    (hρ : ModularCurve.IsDiamondPullbackModL (IsLocalRing.ResidueField ↥A) N H' ρ)
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
        red' ⟨_, h⟩ = ModularCurve.heckeBetaModLH (IsLocalRing.ResidueField ↥A) N H' ℓ (red f)) ∧

      (∀ (γ : CongruenceSubgroup.Gamma0 N) (d : (ZMod N)ˣ), (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = (d : ZMod N) →
        ∀ x : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH N H')), ∃ (f : ↥W) (h : diamondAutHBar N H' d (f : ↥(xHFunctionFieldBar N H')) ∈ W),
          red f = x ∧ red ⟨_, h⟩ = ρ γ x) := by sorry
