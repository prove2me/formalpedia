-- Prove2me | Theorems.Thm_LambdaVaRAmb_Comono_display_15
-- name    : LambdaVaRAmb.Comono.display_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:58.661958+00:00
-- url     : https://prove2.me/theorems/dce756aa-229c-4311-b463-ff9aaebc479f
-- title:
--   (15), p. 40 — if all ΛᵢVaR^{wᵢ}(X) ≥ 0: Σ ΛᵢVaR^{wᵢ}(fᵢ(X)) ≥ Σ fᵢ(ΛᵢVaR^{wᵢ}(X)) ≥ min_{i∈[n]} ΛᵢVaR^{wᵢ}(X)
-- statement:
--   Let $n\ge1$, let $\mathcal X$ be an admissible set of random variables, let $\Lambda_1,\dots,\Lambda_n\in\mathcal H_I$ and let $w_1,\dots,w_n$ be continuous capacities. For every $(f_1,\dots,f_n)\in\mathbb F_n$ and every $X\in\mathcal X$ with $\Lambda_i\mathrm{VaR}^{w_i}(X)\ge0$ for all $i$,
--   $$\sum_{i=1}^n\Lambda_i\mathrm{VaR}^{w_i}(f_i(X))\ \ge\ \sum_{i=1}^n f_i\big(\Lambda_i\mathrm{VaR}^{w_i}(X)\big)\ \ge\ \min_{i\in[n]}\Lambda_i\mathrm{VaR}^{w_i}(X).$$
--
--   Together with the reduction to $\mathbb F_n$ this is the lower bound in (11): no comonotonic split does better than giving all the risk to one agent.
--
--   **Formalization Note** Sums and the minimum are taken in $[-\infty,\infty]$ (`EReal`); the minimum over $[n]$ is `⨅ i : Fin n`. $f_i$ at $+\infty$ is its monotone limit (the values are finite here, since continuity of $w_i$ makes ΛVaR finite from above).
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 40, proof of Theorem 4, display (15)

import Mathlib
import Definitions.Def_LambdaVaRAmb_Comono_Setting

namespace LambdaVaRAmb.Comono

/-- (15), p. 40, for `ΛᵢVaR^{wᵢ}(X) ≥ 0` for all `i`. -/
theorem display_15 {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : LambdaVaRAmb.InfConv.IsRVDomain dom)
    (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)
    (hΛ : ∀ i, LambdaVaRAmb.Robust.InHI (Λ i)) (hw : ∀ i, LambdaVaRAmb.InfConv.IsContinuousCapacity (w i)) :
    ∀ f ∈ splitsFn n, ∀ X ∈ dom, (∀ i, 0 ≤ LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X) →
      ∑ i, extendEReal (f i) (LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X) ≤
          ∑ i, LambdaVaRAmb.Robust.LVaR (Λ i) (w i) (fun ω => f i (X ω)) ∧
        ⨅ i, LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X ≤ ∑ i, extendEReal (f i) (LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X) := by sorry

end LambdaVaRAmb.Comono
