-- Prove2me | Theorems.Thm_LambdaVaRAmb_Comono_reduction_to_Fn
-- name    : LambdaVaRAmb.Comono.reduction_to_Fn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:05.434448+00:00
-- url     : https://prove2.me/theorems/f9004a1c-5d22-4dcd-93c9-4dd5078e01fb
-- title:
--   Proof of Theorem 4, p. 39 — ⊞ᵢ ΛᵢVaR^{wᵢ}(X) is the infimum of Σᵢ ΛᵢVaR^{wᵢ}(fᵢ(X)) over splits (f₁,…,fₙ) ∈ 𝔽ₙ
-- statement:
--   Let $n\ge1$, let $\mathcal X$ be an admissible set of random variables, let $\Lambda_1,\dots,\Lambda_n\in\mathcal H_I$ and let $w_1,\dots,w_n$ be continuous capacities. For every $X\in\mathcal X$,
--   $$\boxplus_{i=1}^n\Lambda_i\mathrm{VaR}^{w_i}(X)=\inf\Big\{\sum_{i=1}^n\Lambda_i\mathrm{VaR}^{w_i}(f_i(X)):(f_1,\dots,f_n)\in\mathbb F_n\Big\},$$
--   where $\mathbb F_n$ is the set of tuples of increasing continuous functions with $f_i(0)=0$ and $f_1+\dots+f_n=\mathrm{id}$, and $\boxplus$ is the infimum over comonotonic same-sign allocations of $X$.
--
--   This is the first step of the proof of Theorem 4: it turns the optimisation over comonotonic allocations into one over splits of the identity. The paper attributes it to the comonotonic assumption and Proposition 4.5 of Denneberg.
--
--   **Formalization Note** Values are in $[-\infty,\infty]$ (`EReal`). The hypotheses $\Lambda_i\in\mathcal H_I$ and continuity of $w_i$ are those of Theorem 4 and are kept as on the page.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 39, proof of Theorem 4, the display after "Using the comonotonic assumption and Proposition 4.5 of Denneberg (2012), we have"

import Mathlib
import Definitions.Def_LambdaVaRAmb_Comono_Setting

namespace LambdaVaRAmb.Comono

/-- Proof of Theorem 4, p. 39: the comonotonic inf-convolution is an infimum over splits in 𝔽ₙ. -/
theorem reduction_to_Fn {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : LambdaVaRAmb.InfConv.IsRVDomain dom)
    (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)
    (hΛ : ∀ i, LambdaVaRAmb.Robust.InHI (Λ i)) (hw : ∀ i, LambdaVaRAmb.InfConv.IsContinuousCapacity (w i)) :
    ∀ X ∈ dom, comonoInfConv dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X =
      ⨅ f ∈ splitsFn n, ∑ i, LambdaVaRAmb.Robust.LVaR (Λ i) (w i) (fun ω => f i (X ω)) := by sorry

end LambdaVaRAmb.Comono
