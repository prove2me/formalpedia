-- Prove2me | Theorems.Thm_ModularCurve_twist_correspondence_heckeT_eq_genDiffModL_T_of_atkinLehnerPinAlong
-- name    : ModularCurve.twist_correspondence_heckeT_eq_genDiffModL_T_of_atkinLehnerPinAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/d021dad9-543d-5320-a8ec-a86d264939c2
-- title:
--   A pinned twist intertwines the transposed ℓ-correspondence with T_ℓ
-- statement:
--   Fix a prime $p$, a nonzero modulus $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is $1$; let $K$ be an algebraically closed field of characteristic $p$, regarded as a $\mathbb{Z}/p$-algebra, and $S$ a set of natural numbers. Write $H'$ for the image of $H$ in $(\mathbb{Z}/(M/p))^\times$ and $\Omega^{\mathrm{ss}}$ for [`ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) H') p`](def/ModularCurve_XHDifferentialsModL.html#L35), the $K$-submodule of differentials of the $q$-expansion function field of $\Gamma_{H'}(M/p)$ over $K$ that are regular outside the supersingular places and have at worst simple poles there. The data are: a $K$-linear map $\rho^\infty$ from $K \otimes_{\mathbb{Z}/p}$ [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) to the differentials, satisfying [`ModularCurve.IsInfReductionMap`](def/ModularCurve_XHDifferentialsModL.html#L443) (for every weight-$2$ cusp form $f$ on $\Gamma_H(M)$ in the two-cusp integral set over the subring $\bot \subseteq \mathbb{C}$ and every integral power series $p_f$ whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of $f$, applying `diffQExp` to $\rho^\infty(1 \otimes \bar f)$ gives the Laurent series of $p_f$ over $K$), whose range is exactly $\Omega^{\mathrm{ss}}$; an Atkin–Lehner datum $W_d$ for $(M, M/p)$, that is $R$ with $M = (M/p)R$ and integers $a,b$ with $(M/p)a - Rb = 1$; a unit $e \in (\mathbb{Z}/M)^\times$ whose image in $\mathbb{Z}/(M/p)$ is inverse to $p$; a ring homomorphism $\varphi$ from the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ to $K$ with $\varphi(p) = 0$; and a $K$-linear automorphism $W$ of $\Omega^{\mathrm{ss}}$ subject to the pinning condition that for every such $f$, every $D$ with $p \nmid D$, every power series $P$ over the algebraic integers whose image in $\mathbb{C}[[q]]$ is the width-one $q$-expansion of $D \cdot (\langle e \rangle f)\mid_2 W_d$, and every $\omega \in \Omega^{\mathrm{ss}}$ equal to $\rho^\infty(1 \otimes \bar f)$, one has $D \cdot \mathrm{diffQExp}(W\omega) = \varphi(P)$ as a Laurent series; finally it is assumed that the $\omega$ arising in this way span $\Omega^{\mathrm{ss}}$ over $K$. The conclusion is that for every prime $\ell \notin S$ with $\ell \nmid M$ and all $\omega, \omega' \in \Omega^{\mathrm{ss}}$ whose underlying differentials satisfy $\omega' = (\mathrm{tr}_\alpha \circ \beta^*)(\omega)$, where $\alpha =$ `heckeAlphaModLH` and $\beta =$ `heckeBetaModLH` at level $\Gamma_{H'}(M/p)$ and $\ell$, one has $W\omega' =$ [`ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.T ℓ …) (W ω)`](def/ModularCurve_XHDifferentialsModL.html#L266), the latter operator being the correspondence $\mathrm{tr}_\beta \circ \alpha^*$.
--
--   This is the transport law for the mod-$p$ Atkin–Lehner twist on supersingular-polar differentials: a twist pinned by its effect on $q$-expansions of Atkin–Lehner images of integral weight-two cusp forms conjugates the transposed Hecke correspondence at a prime $\ell \nmid M$ into the cotangent Hecke operator $T_\ell$ at level $\Gamma_{H'}(M/p)$. It feeds the construction of a twist realising all transposed Hecke generators, used in the level-lowering step of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_twist_correspondence_heckeT_eq_genDiffModL_T_of_atkinLehnerPinAlong.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.twist_correspondence_heckeT_eq_genDiffModL_T_of_atkinLehnerPinAlong
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K] (S : Set ℕ)

    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (hrange : LinearMap.range ρinf = ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)

    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)

    (φ : ↥(integralClosure ℤ ℂ) →+* K) (hφ : φ (p : ↥(integralClosure ℤ ℂ)) = 0)

    (W : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) ≃ₗ[K] ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hW :
      ∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D)
          (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) →
          ∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p), ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
                ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) →
            (D : K) • ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              HahnSeries.ofPowerSeries ℤ K (pfW.map φ))

    (hspan : Submodule.span K {ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) |
        ∃ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D) (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) ∧
          ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
            ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
              ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)} = ⊤)
    :

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)), ((ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
          haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
          AlgebraicCurve.Differential.correspondence (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ) (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ)) ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) →
        ((W ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])) := by sorry
