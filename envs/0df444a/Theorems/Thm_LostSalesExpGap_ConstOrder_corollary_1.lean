-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_corollary_1
-- name    : LostSalesExpGap.ConstOrder.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:10:31.50074+00:00
-- url     : https://prove2.me/theorems/86dbcd5b-4ed3-4af7-9d2e-f80849f4bf7c
-- title:
--   Corollary 1, p. 15 — exponential demand: C(π_r∞) = λ⁻¹(√(h(2p+h)) − h) and bound (9)
-- statement:
--   Suppose the demand $D$ is exponentially distributed with rate $\lambda>0$, and let $h,p>0$, $L\ge1$. Let
--   $$
--   \tau_{p,h}=\sqrt{\frac{h}{2p+h}},\qquad\gamma_{p,h}=(1-\tau_{p,h})\exp(\tau_{p,h}).
--   $$
--   Then $C(\pi_{r_\infty})=\lambda^{-1}\big(\sqrt{h(2p+h)}-h\big)$, and for all $L\ge1$
--   $$
--   \frac{C(\pi_{r_\infty})}{\mathrm{OPT}(L)}\le1+\Big(\tau_{p,h}+(\tau_{p,h}^{-1}-1)\big(e(L+1)\big)^{-1}\Big)\Big((1-\gamma_{p,h})\log(1+ph^{-1})\Big)^{-1}\gamma_{p,h}^{L+1}.
--   $$
--
--   This is Theorem 1 made fully explicit for exponential demand; for example at $p=h=1$, $L=1$ the bound is about $3.36$.
--
--   **Formalization Note** The demand law is the pushforward of Mathlib's exponential distribution to $[0,\infty)$. The ratio is taken in $[0,\infty]$, and $\mathrm{OPT}(L)$ ranges over all measurable history-dependent randomized policies (a class containing the paper's $\Pi$), so the bound is at least as strong as printed.
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Sec. 5.1, Corollary 1, eq. (9), p. 15

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Corollary 1 (Case of exponentially distributed demand), p. 15: if `D` is exponentially
distributed with rate `λ > 0`, then `C(π_{r∞}) = λ⁻¹(√(h(2p + h)) − h)`, and for every `L ≥ 1`
(9) `C(π_{r∞})/OPT(L) ≤ 1 + (τ_{p,h} + (τ_{p,h}⁻¹ − 1)(e(L+1))⁻¹)((1 − γ_{p,h}) log(1 + p h⁻¹))⁻¹ γ_{p,h}^{L+1}`,
the ratio taken in `[0, ∞]`. -/
theorem corollary_1 (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (rate : ℝ) (hrate : 0 < rate)
    (hlaw : P.law = (ProbabilityTheory.expMeasure rate).map Real.toNNReal) :
    constCost P c (rInf P c) =
        ENNReal.ofReal (rate⁻¹ * (Real.sqrt (c.h * (2 * c.p + c.h)) - c.h)) ∧
      constCost P c (rInf P c) / CappedBaseStock.OPT P c ≤
        ENNReal.ofReal (1 + (tauPH c + ((tauPH c)⁻¹ - 1) * (Real.exp 1 * ((c.L : ℝ) + 1))⁻¹) *
          ((1 - gammaPH c) * Real.log (1 + c.p * c.h⁻¹))⁻¹ * gammaPH c ^ (c.L + 1)) := by sorry

end LostSalesExpGap.ConstOrder
