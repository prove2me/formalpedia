-- Prove2me | Theorems.Thm_LambdaVaRAmb_Comono_display_14_all_X
-- name    : LambdaVaRAmb.Comono.display_14_all_X
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:47.97371+00:00
-- url     : https://prove2.me/theorems/1caa4c0b-5562-47a7-bf23-359ae9850ef3
-- title:
--   (14) and (15) for all X, p. 40 — if every Λᵢ is constant on (−∞,0); the conclusion only, the printed intermediate step is replaced, see MODERATION_NOTES
-- statement:
--   Let $n\ge1$, let $\mathcal X$ be an admissible set of random variables, let $\Lambda_1,\dots,\Lambda_n\in\mathcal H_I$ and let $w_1,\dots,w_n$ be continuous capacities. Suppose each $\Lambda_i$ is constant on $(-\infty,0)$. Then for every $(f_1,\dots,f_n)\in\mathbb F_n$, every agent $i$ and every $X\in\mathcal X$ (with no sign condition on $\Lambda_i\mathrm{VaR}^{w_i}(X)$),
--   $$\Lambda_i\mathrm{VaR}^{w_i}(f_i(X))=f_i\big((\Lambda_i\circ f_i)\mathrm{VaR}^{w_i}(X)\big)\ge f_i\big(\Lambda_i\mathrm{VaR}^{w_i}(X)\big),\tag{14}$$
--   and for every $(f_1,\dots,f_n)\in\mathbb F_n$ and every $X\in\mathcal X$,
--   $$\sum_{i=1}^n\Lambda_i\mathrm{VaR}^{w_i}(f_i(X))\ \ge\ \sum_{i=1}^n f_i\big(\Lambda_i\mathrm{VaR}^{w_i}(X)\big)\ \ge\ \min_{i\in[n]}\Lambda_i\mathrm{VaR}^{w_i}(X).\tag{15}$$
--
--   This is the claim "(14) and (15) are valid for all $X\in\mathcal X$" made on p. 40 for the sufficiency part of Theorem 4.
--
--   **Formalization Note** Only the conclusion is posed. The page derives it from "$\Lambda_i\circ f_i\le\Lambda_i$", which fails when $\Lambda_i$ jumps at $0$ and $f_i$ vanishes on part of $(-\infty,0)$; the conclusion is nevertheless true. "Constant on $(-\infty,0)$" is $\Lambda_i(x)=\Lambda_i(y)$ for all $x,y<0$, with nothing said at $0$. $f_i$ at $\pm\infty$ is its monotone limit. Sums and the minimum over $[n]$ (`⨅ i : Fin n`) are in $[-\infty,\infty]$ (`EReal`); no term is $+\infty$, since continuity of $w_i$ makes every ΛVaR here finite from above.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 40, proof of Theorem 4, "Note that if Λ_i, i = 1 . . . , n, are all constants over (−∞, 0) … Hence, (14) and (15) are valid for all X ∈ 𝒳"

import Mathlib
import Definitions.Def_LambdaVaRAmb_Comono_Setting

namespace LambdaVaRAmb.Comono

/-- p. 40: if every `Λᵢ` is constant on `(-∞, 0)`, then (14) and (15) hold for all `X ∈ 𝒳`. -/
theorem display_14_all_X {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : LambdaVaRAmb.InfConv.IsRVDomain dom)
    (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)
    (hΛ : ∀ i, LambdaVaRAmb.Robust.InHI (Λ i)) (hw : ∀ i, LambdaVaRAmb.InfConv.IsContinuousCapacity (w i))
    (hconst : ∀ i, ∀ x y, x < 0 → y < 0 → Λ i x = Λ i y) :
    (∀ f ∈ splitsFn n, ∀ i, ∀ X ∈ dom,
      LambdaVaRAmb.Robust.LVaR (Λ i) (w i) (fun ω => f i (X ω)) =
          extendEReal (f i) (LambdaVaRAmb.Robust.LVaR (fun x => Λ i (f i x)) (w i) X) ∧
        extendEReal (f i) (LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X) ≤
          extendEReal (f i) (LambdaVaRAmb.Robust.LVaR (fun x => Λ i (f i x)) (w i) X)) ∧
    (∀ f ∈ splitsFn n, ∀ X ∈ dom,
      ∑ i, extendEReal (f i) (LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X) ≤
          ∑ i, LambdaVaRAmb.Robust.LVaR (Λ i) (w i) (fun ω => f i (X ω)) ∧
        ⨅ i, LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X ≤
          ∑ i, extendEReal (f i) (LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X)) := by sorry

end LambdaVaRAmb.Comono
