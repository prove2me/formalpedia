-- Prove2me | Theorems.Thm_ModularCurve_twist_genDiffModL_dia_inv_eq_genDiffModL_dia_of_atkinLehnerPinAlong
-- name    : ModularCurve.twist_genDiffModL_dia_inv_eq_genDiffModL_dia_of_atkinLehnerPinAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/c14718f5-305c-5b46-bfcd-426a78fbf7b8
-- title:
--   Pinned twist sends ⟨ d⁻¹⟩ to ⟨ d⟩
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is $1$, an algebraically closed field $K$ of characteristic $p$ with its $\mathbb{Z}/p$-algebra structure, and a set $S$ of naturals; write $H'$ for the image of $H$ in $(\mathbb{Z}/(M/p))^\times$ ([`ModularCurve.infSubgroup`](def/ModularCurve_XHDifferentialsModL.html#L246)) and $\Omega^{\mathrm{ss}}$ for the $K$-subspace [`ModularCurve.ssPolarDifferentials`](def/ModularCurve_XHDifferentialsModL.html#L35) of $\Omega_{F/K}$, $F$ the $q$-expansion function field of level $\Gamma_{H'}(M/p)$, consisting of differentials regular outside the supersingular places and with at worst simple poles there. Assumed are: a $K$-linear map $\rho^\infty$ from $K \otimes_{\mathbb{Z}/p}$ [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) to $\Omega_{F/K}$ which is an `IsInfReductionMap`, i.e. sends $1 \otimes \bar f$, for $f$ a weight-$2$ cusp form on $\Gamma_H(M)$ lying in the two-cusp integral set over the trivial subring and $pf$ an integral $q$-expansion of $f$, to a differential whose $q$-expansion [`ModularCurve.diffQExp`](def/ModularCurve_HeckeDifferential.html#L128) is the reduction of $pf$, and whose range is exactly $\Omega^{\mathrm{ss}}$; an Atkin–Lehner datum $Wd$ for $(M, M/p)$, that is $R$ with $M = (M/p)R$ and integers $a, b$ with $(M/p)a - Rb = 1$; a unit $e \in (\mathbb{Z}/M)^\times$ whose image mod $M/p$ is inverse to $p$; a ring homomorphism $\varphi$ from the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ to $K$ killing $p$; and a $K$-linear automorphism $W$ of $\Omega^{\mathrm{ss}}$ subject to the pinning condition that whenever $f$ is in the two-cusp integral set, $D$ is a natural number prime to $p$, $pfW$ is a power series over that integral closure whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of $D \cdot (\langle e \rangle f)|_2 Wd$ (via [`ModularForm.alSlash`](def/ModularForm_AtkinLehnerDatum.html#L141) and [`CuspForm.diamondLinH`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132)), and $\omega \in \Omega^{\mathrm{ss}}$ equals $\rho^\infty(1 \otimes \bar f)$, then $D \cdot \mathrm{diffQExp}(W\omega) = \varphi(pfW)$; finally such $\omega$ are assumed to span $\Omega^{\mathrm{ss}}$ over $K$. The conclusion is that for every $d \in (\mathbb{Z}/M)^\times$ and all $\omega, \omega' \in \Omega^{\mathrm{ss}}$, if $\omega' = \langle d^{-1} \rangle \omega$ then $W\omega' = \langle d \rangle (W\omega)$, where $\langle d \rangle$ denotes [`ModularCurve.genDiffModL`](def/ModularCurve_XHDifferentialsModL.html#L266) at the generator `CohCarrier.Gen.dia`, namely the diamond operator on $\Omega_{F/K}$ attached to the image of $d$ in $(\mathbb{Z}/(M/p))^\times$.
--
--   This is the mod $p$ form of the Atkin–Li commutation relation $w\langle d\rangle w^{-1} = \langle d^{-1}\rangle$ for the Atkin–Lehner involution at $p$, expressed for the twisting map $W$ on supersingular-polar differentials of the level-$\Gamma_{H'}(M/p)$ curve. It is used in assembling the twisting equivalence that intertwines the diamond and Hecke actions, and in the companion statement treating the operators $T_\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_twist_genDiffModL_dia_inv_eq_genDiffModL_dia_of_atkinLehnerPinAlong.lean

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

theorem ModularCurve.twist_genDiffModL_dia_inv_eq_genDiffModL_dia_of_atkinLehnerPinAlong
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

      (∀ (d : (ZMod M)ˣ) (ω ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)), ((ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia d⁻¹) ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) →
        ((W ω' : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) = ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia d) ((W ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])) := by sorry
