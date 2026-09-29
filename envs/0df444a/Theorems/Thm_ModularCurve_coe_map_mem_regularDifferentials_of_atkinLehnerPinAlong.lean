-- Prove2me | Theorems.Thm_ModularCurve_coe_map_mem_regularDifferentials_of_atkinLehnerPinAlong
-- name    : ModularCurve.coe_map_mem_regularDifferentials_of_atkinLehnerPinAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/07e50f18-8709-5168-954a-4cfc87a02a26
-- title:
--   Atkin–Lehner pin preserves regularity of supersingular-polar differentials
-- statement:
--   Let $p$ be a prime and $M$ a positive integer with $p \mid M$ and $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^\times$ contain every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is $1$, and let $K$ be an algebraically closed field of characteristic $p$, viewed as a $\mathbb{Z}/p$-algebra. Write $\Gamma' =$ [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) of level $M/p$ for the image subgroup [`ModularCurve.infSubgroup p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L246), $F =$ [`ModularCurve.qExpFunctionFieldC K Γ'`](def/ModularCurve_X1.html#L101), and $\Omega^{\mathrm{ss}} =$ [`ModularCurve.ssPolarDifferentials K Γ' p`](def/ModularCurve_XHDifferentialsModL.html#L35), the $K$-submodule of $\Omega[F/K]$ of differentials regular at every place of $F/K$ outside the supersingular places `ssPlacesQExp` and with at most a simple pole at each of those. Assume given a $K$-linear map $\rho^\infty$ from $K \otimes_{\mathbb{Z}/p}$ [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) to $\Omega[F/K]$ which is an `IsInfReductionMap` (for every weight-$2$ cusp form $f$ on `GammaH M H` in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54) and every $pf \in \mathbb{Z}[[q]]$ with `IsIntegralQExp f pf`, the $q$-expansion `diffQExp` of $\rho^\infty(1 \otimes \mathrm{intTwoCuspReduce}\,f)$ is `intSeriesC K pf`) and whose range is exactly $\Omega^{\mathrm{ss}}$. Let $W_d$ be an Atkin–Lehner datum for $(M, M/p)$, that is, $R$ with $M = (M/p)R$ and integers $a,b$ with $(M/p)a - Rb = 1$; let $e \in (\mathbb{Z}/M)^\times$ have image $\bar e$ in $\mathbb{Z}/(M/p)$ satisfying $\bar e\,\bar p = 1$; let $\varphi$ be a ring homomorphism from the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ to $K$ with $\varphi(p) = 0$. Let $W_\ell$ be a $K$-linear endomorphism of $\Omega^{\mathrm{ss}}$ satisfying the pinning condition: for every such $f$, every $D \in \mathbb{N}$ with $p \nmid D$, and every power series $pf_W$ over the algebraic integers whose image in $\mathbb{C}[[q]]$ is the width-one $q$-expansion of $(D:\mathbb{C}) \cdot \mathrm{alSlash}\,W_d\,2\,(\mathrm{diamondLinH}\,2\,e\,f)$, and every $\omega \in \Omega^{\mathrm{ss}}$ whose underlying differential equals $\rho^\infty(1 \otimes \mathrm{intTwoCuspReduce}\,f)$, one has $D \cdot \mathrm{diffQExp}(W_\ell \omega) = \mathrm{ofPowerSeries}(\varphi_*\,pf_W)$. Then for every $\omega \in \Omega^{\mathrm{ss}}$ whose underlying differential lies in [`AlgebraicCurve.regularDifferentials K F`](def/AlgebraicCurve_RegularDifferentials.html#L26) — that is, at each place $v$ it is $f \cdot v.\mathrm{dCoord}$ for some $f$ in the valuation subring of $v$ — the differential underlying $W_\ell \omega$ again lies in [`AlgebraicCurve.regularDifferentials K F`](def/AlgebraicCurve_RegularDifferentials.html#L26).
--
--   This is the forward implication of the regularity clause for the mod-$p$ Atkin–Lehner twist on supersingular-polar differentials on $X_{H'}(M/p)$ over $K$: the twist, characterised by its effect on $q$-expansions of two-cusp integral weight-$2$ forms, carries regular differentials to regular differentials. It feeds [`ModularCurve.mem_regularDifferentials_iff_of_atkinLehnerPinAlong`](thm.html#ModularCurve.mem_regularDifferentials_iff_of_atkinLehnerPinAlong), where the converse is obtained from bijectivity, in the analysis of the mod-$p$ cohomology of modular curves at a prime exactly dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coe_map_mem_regularDifferentials_of_atkinLehnerPinAlong.lean

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

theorem ModularCurve.coe_map_mem_regularDifferentials_of_atkinLehnerPinAlong
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
    (ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hω : ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) ∈
      AlgebraicCurve.regularDifferentials K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))
    :
    ((Wl ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) ∈
      AlgebraicCurve.regularDifferentials K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) := by sorry
