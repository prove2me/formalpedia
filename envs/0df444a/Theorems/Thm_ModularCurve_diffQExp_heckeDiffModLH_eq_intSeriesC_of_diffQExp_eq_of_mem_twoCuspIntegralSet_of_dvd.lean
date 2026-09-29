-- Prove2me | Theorems.Thm_ModularCurve_diffQExp_heckeDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet_of_dvd
-- name    : ModularCurve.diffQExp_heckeDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/5985a3e6-4499-524a-b4e8-c2dc9a2276a2
-- title:
--   U_q on differentials mod p matches U_q on q-expansions
-- statement:
--   Fix a prime $p$ and $M\ge 1$ with $p\mid M$, $p^2\nmid M$, and a subgroup $H\le(\mathbb{Z}/M)^\times$ such that every unit mapping to $1$ under the reduction $(\mathbb{Z}/M)^\times\to(\mathbb{Z}/(M/p))^\times$ lies in $H$; let $K$ be an algebraically closed field of characteristic $p$. Write $\Gamma_H(M)\le \mathrm{SL}_2(\mathbb{Z})$ for the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under $\Gamma_0(M)\to(\mathbb{Z}/M)^\times$, $\gamma\mapsto d$, and $H'=$ `infSubgroup p M H hpM` for the image of $H$ in $(\mathbb{Z}/(M/p))^\times$. Let $f$ be a weight-two cusp form for $\Gamma_H(M)$ lying in [`CuspForm.twoCuspIntegralSet M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L54), i.e. for every $t$ in the Hecke ring `heckeRingH M H 2`, every Atkin–Lehner datum $W$ at $p$ and every $n$, the $n$-th $q$-coefficients of $t f$ and of $W$ applied to $t f$ in weight two lie in the bottom subring of $\mathbb{C}$; let $pf,pqf\in\mathbb{Z}[[q]]$ have complex images equal to the $q$-expansions of $f$ and of [`CuspForm.heckeULinH 2 q f`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171) respectively, where $q$ is a prime dividing $M$ with $q\ne p$. Let $\omega$ be a Kähler differential of the $q$-expansion function field `qExpFunctionFieldC K (CohCarrier.GammaH (M/p) H')` over $K$ whose $q$-expansion `diffQExp` equals the coefficientwise reduction `intSeriesC K pf`. Then the $q$-expansion of `heckeDiffModLH K (M/p) H' q ω`, the correspondence $\mathrm{tr}_\beta\circ\alpha^*$ at $q$ on differentials, equals `intSeriesC K pqf`.
--
--   This is the $q$-expansion form of the compatibility, away from $p$, between the Hecke operator $U_q$ on weight-two cusp forms of level $\Gamma_H(M)$ and the Hecke correspondence $U_q$ on differentials of the characteristic-$p$ $q$-expansion function field attached to $\Gamma_{H'}(M/p)$, the component through the cusp $\infty$ of the reduction. It feeds the comparison of Hecke actions used in [`ModularCurve.IsInfReductionMap.comp_baseChange_genU_eq_genDiffModL_comp_of_ne`](thm.html#ModularCurve.IsInfReductionMap.comp_baseChange_genU_eq_genDiffModL_comp_of_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diffQExp_heckeDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.diffQExp_heckeDiffModLH_eq_intSeriesC_of_diffQExp_eq_of_mem_twoCuspIntegralSet_of_dvd
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp f pf)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p) (pqf : PowerSeries ℤ)
    (hpqf : ModularCurve.IsIntegralQExp (CuspForm.heckeULinH 2 q f) pqf)
    (ω : Ω[ModularCurve.qExpFunctionFieldC K
      (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hω : ModularCurve.diffQExp
      (ModularCurve.qExpFunctionFieldC K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) ω =
        ModularCurve.intSeriesC K pf) :
    ModularCurve.diffQExp
        (ModularCurve.qExpFunctionFieldC K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
        ((haveI : NeZero q := ⟨hq.ne_zero⟩;
          ModularCurve.heckeDiffModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q) ω) =
      ModularCurve.intSeriesC K pqf := by sorry
