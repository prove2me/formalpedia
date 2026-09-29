-- Prove2me | Theorems.Thm_FoundationsML_SVM_rademacher_complexity_bounded_linear_hypotheses
-- name    : FoundationsML.SVM.rademacher_complexity_bounded_linear_hypotheses
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:31:10.632229+00:00
-- url     : https://prove2.me/theorems/2860fc2b-a753-42de-94cc-05d70dd7edd5
-- title:
--   Theorem 5.10 — Rademacher complexity of norm-bounded linear hypotheses
-- statement:
--   **Statement (Theorem 5.10, p. 97, PDF p. 114).** Let $S\subseteq\{x:\|x\|\le r\}$ be a
--   sample of size $m$ and let $H=\{x\mapsto w\cdot x:\|w\|\le\Lambda\}$. Then
--   $$\hat R_S(H) \le \sqrt{\frac{r^2\Lambda^2}{m}}.$$
--
--   This bounds the empirical Rademacher complexity of bounded-norm linear hypotheses via
--   Cauchy-Schwarz and Jensen's inequality, feeding directly into Corollary 5.11's margin bound
--   for linear hypotheses.
--
--   **Formalization Note.** `X` is a real inner-product space (generalizing the book's
--   $\mathbb R^N$); `H` is written as `{h | ∃ w, ‖w‖ ≤ Λ ∧ h = fun x => inner ℝ w x}` rather than
--   a `Set.image`, to match the book's set-builder notation directly.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 97, Theorem 5.10 (PDF p. 114)

import Mathlib
import Definitions.Def_FoundationsML_SVM_EmpiricalRademacherComplexity

namespace FoundationsML.SVM

/-- Theorem 5.10 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 97, PDF p. 114). Let `S ⊆ {x : ‖x‖ ≤ r}` be a sample of size `m` and let
`H = {x ↦ w · x : ‖w‖ ≤ Λ}`. Then the empirical Rademacher complexity of `H` satisfies
`R̂_S(H) ≤ sqrt(r²Λ²/m)`. -/
theorem rademacher_complexity_bounded_linear_hypotheses
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {m : ℕ} (S : Fin m → X) (r Λ : ℝ) (hr : 0 ≤ r) (hΛ : 0 ≤ Λ)
    (hS : ∀ i, ‖S i‖ ≤ r) :
    EmpiricalRademacherComplexity
        {h : X → ℝ | ∃ w : X, ‖w‖ ≤ Λ ∧ h = fun x => inner ℝ w x} S
      ≤ Real.sqrt (r ^ 2 * Λ ^ 2 / m) := by sorry

end FoundationsML.SVM
