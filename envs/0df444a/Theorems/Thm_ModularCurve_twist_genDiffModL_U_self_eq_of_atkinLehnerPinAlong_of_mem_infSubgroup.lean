-- Prove2me | Theorems.Thm_ModularCurve_twist_genDiffModL_U_self_eq_of_atkinLehnerPinAlong_of_mem_infSubgroup
-- name    : ModularCurve.twist_genDiffModL_U_self_eq_of_atkinLehnerPinAlong_of_mem_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/f09bb0b9-9f2c-5b71-a510-ec9df70b0c6a
-- title:
--   Pinned Atkin–Lehner twist commutes with Uₚ
-- statement:
--   Fix a prime $p$ and $M>0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is $1$, an algebraically closed field $K$ of characteristic $p$ with its $\mathbb{Z}/p$-algebra structure, and a set $S$ of naturals. Write $H' =$ [`ModularCurve.infSubgroup p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L246), the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, and $\Omega^{\mathrm{ss}} =$ [`ModularCurve.ssPolarDifferentials`](def/ModularCurve_XHDifferentialsModL.html#L35), the $K$-submodule of $\Omega_{F/K}$, $F$ the $q$-expansion function field of level $\Gamma_{H'}(M/p)$ over $K$, of differentials regular outside the supersingular places and with at most simple poles there. Assume given a $K$-linear $\rho^\infty$ from $K \otimes_{\mathbb{Z}/p}$ [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) to $\Omega_{F/K}$ which is an `IsInfReductionMap` (for $f$ in the two-cusp integral set, i.e. all Hecke-ring translates of $f$ and of their Atkin–Lehner slashes have $q$-coefficients in the prime subring of $\mathbb{C}$, and an integral $q$-expansion $pf$, the $q$-expansion of $\rho^\infty(1 \otimes \bar f)$ via [`ModularCurve.diffQExp`](def/ModularCurve_HeckeDifferential.html#L128) is `intSeriesC K pf`) with range exactly $\Omega^{\mathrm{ss}}$; an Atkin–Lehner datum $W_d$ for $(M, M/p)$, consisting of $R$ with $M = (M/p)R$ and integers $a,b$ with $(M/p)a - Rb = 1$; a unit $e$ of $\mathbb{Z}/M$ whose image mod $M/p$ is inverse to $p$; a unit $d$ whose image mod $M/p$ equals $p$, with that image or its negative lying in $H'$; a ring homomorphism $\varphi$ from the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ to $K$ killing $p$; and a $K$-linear automorphism $W$ of $\Omega^{\mathrm{ss}}$ subject to the pinning condition: whenever $f$ lies in the two-cusp integral set of weight $2$, $D$ is a natural number prime to $p$, and a power series $pf_W$ over the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ has complex image equal to the $q$-expansion (period $1$) of $D \cdot (\langle e \rangle f)\,|_2\,W_d$, then for every $\omega \in \Omega^{\mathrm{ss}}$ with underlying differential $\rho^\infty(1 \otimes \bar f)$ one has $D \cdot \mathrm{diffQExp}(W\omega) = \varphi(pf_W)$ as a Laurent series; assume further that the $\omega$ so pinned span $\Omega^{\mathrm{ss}}$ over $K$. The conclusion is that for all $\omega, \omega' \in \Omega^{\mathrm{ss}}$, if $\omega' =$ [`ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p _ hpM)`](def/ModularCurve_XHDifferentialsModL.html#L266) applied to $\omega$ — the operator attached to the generator $U_p$, which at the generator's own prime is the Frobenius push-forward on differentials — then $W\omega'$ is the same operator applied to $W\omega$; that is, $W$ commutes with $U_p$ on $\Omega^{\mathrm{ss}}$. The hypothesis $d$ together with $\mathrm{hd}$, $\mathrm{hdH}$ records that $p$ mod $M/p$ lies in $\pm H'$.
--
--   This is the $U_p$ clause of the compatibility of the mod $p$ Atkin–Lehner twist with the Hecke action on supersingular-polar differentials, in the case where the class of $p$ modulo $M/p$ lies in $\pm H'$, so that the twist commutes with $U_p$ rather than merely normalising it. It is one of the inputs to the construction of the twisting automorphism interchanging the Hecke operators and their transposes on $\Omega^{\mathrm{ss}}$, which is used in the level-lowering argument at the prime $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_twist_genDiffModL_U_self_eq_of_atkinLehnerPinAlong_of_mem_infSubgroup.lean

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

theorem ModularCurve.twist_genDiffModL_U_self_eq_of_atkinLehnerPinAlong_of_mem_infSubgroup
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K] (S : Set ℕ)

    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (hrange : LinearMap.range ρinf = ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)

    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)

    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)

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

      (∀ (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)), ((ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM) ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) →
        ((W ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])) := by sorry
