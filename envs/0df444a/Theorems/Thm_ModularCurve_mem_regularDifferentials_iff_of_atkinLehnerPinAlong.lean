-- Prove2me | Theorems.Thm_ModularCurve_mem_regularDifferentials_iff_of_atkinLehnerPinAlong
-- name    : ModularCurve.mem_regularDifferentials_iff_of_atkinLehnerPinAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/cb25acee-1ab7-5778-b336-3070d403dbb3
-- title:
--   Pinned Atkin–Lehner map preserves and reflects regular differentials
-- statement:
--   Fix a prime $p$ and a modulus $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is trivial, and an algebraically closed field $K$ of characteristic $p$. Write $F =$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))`](def/ModularCurve_X1.html#L101), the $q$-expansion function field at level $\Gamma_{H'}(M/p)$ with $H'$ the image of $H$, and $\Omega^{\mathrm{ss}}$ for `ssPolarDifferentials`, the $K$-submodule of $\Omega_{F/K}$ of differentials regular away from the supersingular places and with at most a simple pole at each of them. The data are: a $K$-linear map $\rho^\infty$ from $K \otimes_{\mathbb{Z}/p}$ [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) to $\Omega_{F/K}$ which is an `IsInfReductionMap` (it carries $1 \otimes$ the reduction of a two-cusp integral weight-$2$ form $f$ with integral $q$-expansion $pf$ to the differential whose $q$-expansion is the reduction of $pf$) and has range exactly $\Omega^{\mathrm{ss}}$; an Atkin–Lehner datum $W_d$ for $(M, M/p)$, i.e. $R$ with $M=(M/p)R$ and integers $a,b$ with $(M/p)a-Rb=1$; a unit $e \in (\mathbb{Z}/M)^\times$ whose image satisfies $\bar{e}\,\bar{p}=1$ in $\mathbb{Z}/(M/p)$; a ring homomorphism $\varphi$ from the algebraic integers $\overline{\mathbb{Z}} \subset \mathbb{C}$ to $K$ with $\varphi(p)=0$; and a $K$-linear endomorphism $W_\ell$ of $\Omega^{\mathrm{ss}}$ subject to the pinning hypothesis: whenever $f$ lies in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54) (all its Hecke translates and their $W$-slashes have $q$-coefficients in the minimal subring of $\mathbb{C}$), $D$ is a natural number prime to $p$, $pfW$ is a power series over $\overline{\mathbb{Z}}$ whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of $D \cdot (W_d$-slash of $\langle e \rangle f)$, and $\omega \in \Omega^{\mathrm{ss}}$ has underlying differential $\rho^\infty(1 \otimes \overline{f})$, then $D$ times the $q$-expansion (`diffQExp`) of $W_\ell \omega$ equals the Laurent series obtained from $pfW$ via $\varphi$. The conclusion is that for every $\omega \in \Omega^{\mathrm{ss}}$, the differential $\omega$ lies in [`AlgebraicCurve.regularDifferentials K F`](def/AlgebraicCurve_RegularDifferentials.html#L26) — i.e. at every place $v$ of $F/K$ it is $f \cdot dv$ for some $f$ in the valuation subring of $v$ — if and only if $W_\ell \omega$ does.
--
--   This upgrades the one-sided statement that the pinned mod-$p$ Atkin–Lehner operator carries regular differentials to regular differentials into an equivalence, so that regularity of a supersingular-polar differential can be tested on its Atkin–Lehner translate; it feeds the construction of the linear equivalence of supersingular-polar differentials compatible with regularity used in the level-lowering argument at a prime exactly dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_regularDifferentials_iff_of_atkinLehnerPinAlong.lean

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

theorem ModularCurve.mem_regularDifferentials_iff_of_atkinLehnerPinAlong
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
      (∀ ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p), ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) ∈ AlgebraicCurve.regularDifferentials K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ↔
        ((Wl ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) ∈ AlgebraicCurve.regularDifferentials K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) := by sorry
