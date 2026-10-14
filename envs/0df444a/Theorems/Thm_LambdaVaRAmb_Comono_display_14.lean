-- Prove2me | Theorems.Thm_LambdaVaRAmb_Comono_display_14
-- name    : LambdaVaRAmb.Comono.display_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:48.018985+00:00
-- url     : https://prove2.me/theorems/7375db83-bb1a-40d7-90de-1e77c72bfb55
-- title:
--   (14), p. 40 — for ΛᵢVaR^{wᵢ}(X) ≥ 0: ΛᵢVaR^{wᵢ}(fᵢ(X)) = fᵢ((Λᵢ∘fᵢ)VaR^{wᵢ}(X)) ≥ fᵢ(ΛᵢVaR^{wᵢ}(X))
-- statement:
--   Let $n\ge1$, let $\mathcal X$ be an admissible set of random variables, let $\Lambda_1,\dots,\Lambda_n\in\mathcal H_I$ and let $w_1,\dots,w_n$ be continuous capacities. For every $(f_1,\dots,f_n)\in\mathbb F_n$, every agent $i$ and every $X\in\mathcal X$ with $\Lambda_i\mathrm{VaR}^{w_i}(X)\ge0$,
--   $$\Lambda_i\mathrm{VaR}^{w_i}(f_i(X))=f_i\big((\Lambda_i\circ f_i)\mathrm{VaR}^{w_i}(X)\big)\ge f_i\big(\Lambda_i\mathrm{VaR}^{w_i}(X)\big).$$
--
--   This is display (14) of the paper under the hypothesis of the first sentence of Theorem 4: no split can lower an agent's risk below the image of its unsplit ΛVaR.
--
--   **Formalization Note** $f_i$ at $\pm\infty$ is its monotone limit (`extendEReal`), which matters when $(\Lambda_i\circ f_i)\mathrm{VaR}^{w_i}(X)$ is infinite, e.g. for $f_i\equiv0$.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 40, proof of Theorem 4, display (14) (derived on p. 39 for x_i ≥ 0)

import Mathlib
import Definitions.Def_LambdaVaRAmb_Comono_Setting

namespace LambdaVaRAmb.Comono

/-- (14), p. 40, for `ΛᵢVaR^{wᵢ}(X) ≥ 0`. -/
theorem display_14 {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : LambdaVaRAmb.InfConv.IsRVDomain dom)
    (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)
    (hΛ : ∀ i, LambdaVaRAmb.Robust.InHI (Λ i)) (hw : ∀ i, LambdaVaRAmb.InfConv.IsContinuousCapacity (w i)) :
    ∀ f ∈ splitsFn n, ∀ i, ∀ X ∈ dom, 0 ≤ LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X →
      LambdaVaRAmb.Robust.LVaR (Λ i) (w i) (fun ω => f i (X ω)) =
          extendEReal (f i) (LambdaVaRAmb.Robust.LVaR (fun x => Λ i (f i x)) (w i) X) ∧
        extendEReal (f i) (LambdaVaRAmb.Robust.LVaR (Λ i) (w i) X) ≤
          extendEReal (f i) (LambdaVaRAmb.Robust.LVaR (fun x => Λ i (f i x)) (w i) X) := by sorry

end LambdaVaRAmb.Comono
