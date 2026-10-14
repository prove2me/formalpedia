-- Prove2me | Theorems.Thm_LambdaVaRAmb_Comono_change_of_variables
-- name    : LambdaVaRAmb.Comono.change_of_variables
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:09.369987+00:00
-- url     : https://prove2.me/theorems/85e28458-4685-472d-840e-7d80f72b5114
-- title:
--   Proof of Theorem 4, p. 39 — for (fᵢ) ∈ 𝔽ₙ, ΛᵢVaR^{wᵢ}(fᵢ(X)) = fᵢ((Λᵢ∘fᵢ)VaR^{wᵢ}(X))
-- statement:
--   Let $n\ge1$, let $\mathcal X$ be an admissible set of random variables, let $\Lambda_1,\dots,\Lambda_n\in\mathcal H_I$ and let $w_1,\dots,w_n$ be continuous capacities. For every $(f_1,\dots,f_n)\in\mathbb F_n$, every agent $i$ and every $X\in\mathcal X$,
--   $$\Lambda_i\mathrm{VaR}^{w_i}(f_i(X))=f_i\big((\Lambda_i\circ f_i)\mathrm{VaR}^{w_i}(X)\big),$$
--   where on the right $f_i$ is evaluated at a point of $[-\infty,\infty]$, with $f_i(-\infty)=\inf_x f_i(x)$ and $f_i(+\infty)=\sup_x f_i(x)$.
--
--   The identity moves the split $f_i$ from the random variable to the level function, so that each agent's risk after the split is a ΛVaR of the original $X$.
--
--   **Formalization Note** $(\Lambda_i\circ f_i)\mathrm{VaR}^{w_i}$ is `LVaR (fun x => Λ i (f i x)) (w i)`. The page applies $f_i$ to a value in $[-\infty,\infty]$ without comment; the Lean uses the monotone limits `extendEReal` of the definition file.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 39, proof of Theorem 4, the display after "It follows from the definition that"

import Mathlib
import Definitions.Def_LambdaVaRAmb_Comono_Setting

namespace LambdaVaRAmb.Comono

/-- Proof of Theorem 4, p. 39: `ΛᵢVaR^{wᵢ}(fᵢ(X)) = fᵢ((Λᵢ ∘ fᵢ)VaR^{wᵢ}(X))` for `f ∈ 𝔽ₙ`. -/
theorem change_of_variables {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : LambdaVaRAmb.InfConv.IsRVDomain dom)
    (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)
    (hΛ : ∀ i, LambdaVaRAmb.Robust.InHI (Λ i)) (hw : ∀ i, LambdaVaRAmb.InfConv.IsContinuousCapacity (w i)) :
    ∀ f ∈ splitsFn n, ∀ i, ∀ X ∈ dom,
      LambdaVaRAmb.Robust.LVaR (Λ i) (w i) (fun ω => f i (X ω)) =
        extendEReal (f i) (LambdaVaRAmb.Robust.LVaR (fun x => Λ i (f i x)) (w i) X) := by sorry

end LambdaVaRAmb.Comono
