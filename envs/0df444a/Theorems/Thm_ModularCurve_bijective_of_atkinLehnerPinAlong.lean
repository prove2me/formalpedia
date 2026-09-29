-- Prove2me | Theorems.Thm_ModularCurve_bijective_of_atkinLehnerPinAlong
-- name    : ModularCurve.bijective_of_atkinLehnerPinAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/e1217f0a-6d9e-5c9b-8990-40e7aef85adf
-- title:
--   Pinned Atkin–Lehner operators on supersingular-polar differentials are bijective
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image under reduction to $(\mathbb{Z}/(M/p))^\times$ is $1$, with $M/p \neq 0$, and let $K$ be an algebraically closed field of characteristic $p$ which is a $\mathbb{Z}/p$-algebra. Write $H'$ for the image of $H$ in $(\mathbb{Z}/(M/p))^\times$ and $\Gamma' = \Gamma_{H'}(M/p) \le \mathrm{SL}_2(\mathbb{Z})$; all differentials below are Kähler differentials of the intermediate field [`ModularCurve.qExpFunctionFieldC`](def/ModularCurve_X1.html#L101) $K$ $\Gamma'$ of $K((q))$ over $K$, and $\Omega^{\mathrm{ss}}$ denotes [`ModularCurve.ssPolarDifferentials`](def/ModularCurve_XHDifferentialsModL.html#L35), the $K$-submodule of those differentials that are regular at every place outside the supersingular set `ssPlacesQExp` and have at worst a simple pole at each place in it. Let $\rho^\infty$ be a $K$-linear map from $K \otimes_{\mathbb{Z}/p} \mathrm{CuspForm.IntTwoCuspForms}\,M\,H\,p$ (the mod-$p$ reduction of the two-cusp lattice of weight-two cusp forms on $\Gamma_H(M)$) to the differentials, assumed to be an `IsInfReductionMap`: for every weight-two cusp form $f$ on $\Gamma_H(M)$ lying in $\mathrm{CuspForm.twoCuspIntegralSet}\,M\,H\,2\,p\,\bot$ (all Hecke translates of $f$, and their Atkin–Lehner slashes, have $q$-coefficients in the prime subring of $\mathbb{C}$) and every integral power series $pf$ that is an integral $q$-expansion of $f$, the $q$-expansion `diffQExp` of $\rho^\infty(1 \otimes \bar f)$ is the reduction of $pf$ over $K$; assume moreover that the range of $\rho^\infty$ is exactly $\Omega^{\mathrm{ss}}$. Fix an Atkin–Lehner datum $W_d$ for $(M, M/p)$, that is $R$ with $M = (M/p)R$ and integers $a,b$ with $(M/p)a - Rb = 1$; a unit $e$ of $\mathbb{Z}/M$ whose image $\bar e$ in $\mathbb{Z}/(M/p)$ satisfies $\bar e \cdot p = 1$; and a ring homomorphism $\varphi$ from the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ to $K$ with $\varphi(p) = 0$. Let $W_\ell$ be a $K$-linear endomorphism of $\Omega^{\mathrm{ss}}$ satisfying the following pinning condition: for every $f$ in the two-cusp integral set as above, every natural number $D$ not divisible by $p$, every power series $pfW$ over the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ whose image in $\mathbb{C}[[q]]$ is the width-one $q$-expansion of $D \cdot \bigl(\langle e \rangle f\bigr)\mid_2 W_d$, and every $\omega \in \Omega^{\mathrm{ss}}$ equal, as a differential, to $\rho^\infty(1 \otimes \bar f)$, one has $D \cdot \mathrm{diffQExp}(W_\ell \omega) = \varphi(pfW)$ as a Laurent series over $K$. Then $W_\ell$ is bijective.
--
--   This is the statement that an Atkin–Lehner involution at the exact level-$p$ part, characterised on the mod-$p$ supersingular-polar differentials of $X_{H'}(M/p)$ by its effect on $q$-expansions, is an automorphism of that space. It is used to produce the corresponding linear equivalence and the resulting criterion for a supersingular-polar differential to be regular, the inputs to the comparison of differentials at level $M$ and level $M/p$ in level lowering at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_bijective_of_atkinLehnerPinAlong.lean

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

theorem ModularCurve.bijective_of_atkinLehnerPinAlong
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]

    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (hrange : LinearMap.range ρinf = ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)

    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)

    (φ : ↥(integralClosure ℤ ℂ) →+* K) (hφ : φ (p : ↥(integralClosure ℤ ℂ)) = 0)
    (Wl : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) →ₗ[K] ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hWl :
      ∀ (f : CuspForm (CohCarrier.GammaH M H) 2)
          (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D)
          (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) →
          ∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p), ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
                ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩) →
            (D : K) • ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ((Wl ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
              HahnSeries.ofPowerSeries ℤ K (pfW.map φ))
    :
    Function.Bijective Wl := by sorry
