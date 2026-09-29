-- Prove2me | Theorems.Thm_ModularCurve_diffQExp_diamondDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet
-- name    : ModularCurve.diffQExp_diamondDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/e206ac35-7d3e-5523-922f-7ca10d6b78ba
-- title:
--   Diamond operators on mod p differentials match ⟨ d⟩ on q-expansions
-- statement:
--   Let $p$ be a prime and $M\ge 1$ with $p\mid M$ and $p^{2}\nmid M$, and let $H\le(\mathbb{Z}/M)^{\times}$ be a subgroup containing every unit whose image under the reduction $(\mathbb{Z}/M)^{\times}\to(\mathbb{Z}/(M/p))^{\times}$ is $1$. Let $K$ be an algebraically closed field of characteristic $p$. Let $f$ be a weight-two cusp form for $\Gamma_H(M)$, the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained from $\Gamma_0(M)$ as the preimage of $H$ under the lower-right-entry character [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121), and assume $f$ lies in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54): for every element $t$ of the Hecke ring `heckeRingH M H 2`, every Atkin–Lehner datum $W$ for $(M,p)$ and every $n$, the $n$-th $q$-coefficients of $t f$ and of $W$ applied to $t f$ in weight $2$ lie in the subring $\bot\subseteq\mathbb{C}$, i.e. are rational integers. Let $pf\in\mathbb{Z}[[q]]$ have $\mathbb{C}$-image the $q$-expansion of $f$, let $d\in(\mathbb{Z}/M)^{\times}$, and let $pdf\in\mathbb{Z}[[q]]$ likewise represent the $q$-expansion of $\langle d\rangle f$, the slash action of a lift of $d$ to $\Gamma_0(M)$ as given by [`CuspForm.diamondLinH`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132). Write $H'$ for the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$ and $F$ for the $q$-expansion function field [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M/p) H')`](def/ModularCurve_X1.html#L101), generated over $K$ by the reductions of integral ratios of forms. If $\omega\in\Omega^{1}_{F/K}$ has $q$-expansion [`ModularCurve.diffQExp`](def/ModularCurve_HeckeDifferential.html#L128) equal to the reduction of $pf$ in $K((q))$, then the $q$-expansion of the pullback of $\omega$ along the automorphism of $F$ attached by [`ModularCurve.diamondDiffModLH`](def/ModularCurve_XHDifferentialsModL.html#L231) to the image of $d$ in $(\mathbb{Z}/(M/p))^{\times}$ equals the reduction of $pdf$ in $K((q))$.
--
--   This is the $q$-expansion form of the statement that, on the component through $\infty$ of the special fibre at $p$ of the model of $X_H(M)$, the diamond operator $\langle d\rangle$ of level $M$ induces the diamond operator of level $M/p$ indexed by $d \bmod (M/p)$, transported to differentials. It is used in the level-lowering package: in the identification of the two-component regular differentials attached to two-cusp integral forms, in the comparison of the Hecke action with its mod $p$ counterpart, and in the corresponding statement for the Hecke operators $T_\ell$ with $\ell\nmid M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diffQExp_diamondDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.diffQExp_diamondDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp f pf)
    (d : (ZMod M)ˣ) (pdf : PowerSeries ℤ)
    (hpdf : ModularCurve.IsIntegralQExp (CuspForm.diamondLinH 2 d f) pdf)
    (ω : Ω[ModularCurve.qExpFunctionFieldC K
      (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hω : ModularCurve.diffQExp
      (ModularCurve.qExpFunctionFieldC K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ω =
        ModularCurve.intSeriesC K pf) :
    ModularCurve.diffQExp
        (ModularCurve.qExpFunctionFieldC K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
        ((haveI : NeZero (M / p) := ModularCurve.neZero_div p M hpM;
          ModularCurve.diamondDiffModLH K (M / p) (ModularCurve.infSubgroup p M H hpM)
            (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)) ω) =
      ModularCurve.intSeriesC K pdf := by sorry
