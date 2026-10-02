-- Prove2me | Theorems.Thm_LeblSCV_Pseudoconvex_psh_smoothing
-- name    : LeblSCV.Pseudoconvex.psh_smoothing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T05:31:17.557992+00:00
-- url     : https://prove2.me/theorems/14c3f881-294e-4fb4-bfff-9b831f758396
-- title:
--   Theorem 2.4.10 — smoothing plurisubharmonic functions
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open and $f : U \to \mathbb{R} \cup \{-\infty\}$ plurisubharmonic. Let $U_\epsilon \subset U$ be the set of points further than $\epsilon > 0$ from $\partial U$. Then for every $\epsilon > 0$ there is a smooth plurisubharmonic $f_\epsilon : U_\epsilon \to \mathbb{R}$ with $f_\epsilon(z) \ge f(z)$, and
--   $$f(z) = \lim_{\epsilon \to 0} f_\epsilon(z) \qquad \text{for all } z \in U.$$
--
--   Every plurisubharmonic function is therefore a pointwise limit of smooth ones. This is how statements about $C^2$ plurisubharmonic functions are extended to all of them.
--
--   **Formalization Note.** **Formalization Note.** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, so its norm, balls and distances are Euclidean, as in the book. Values in $\mathbb{R}\cup\{-\infty\}$ are modelled in `EReal` together with the requirement $f \neq +\infty$ on $U$; upper semicontinuity is Mathlib's `UpperSemicontinuousOn` for the order of `EReal`. The family $\{f_\epsilon\}$ is a single function $F : \mathbb{R} \to \mathbb{C}^n \to \mathbb{R}$. Smooth is `ContDiffOn ℝ ∞` on $U_\epsilon$. The limit is $\epsilon \to 0^+$ in `EReal`, which also covers the points where $f(z) = -\infty$. For each $z \in U$ the limit only involves small $\epsilon$, for which $z \in U_\epsilon$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 85, Theorem 2.4.10

import Mathlib
import Definitions.Def_LeblSCV_Pseudoconvex_IsPlurisubharmonicOn
import Definitions.Def_LeblSCV_Pseudoconvex_awayFromBoundary

open scoped ContDiff Topology

namespace LeblSCV.Pseudoconvex

/-- Theorem 2.4.10 (Lebl, p. 85). Let `U ⊂ ℂⁿ` be open and `f : U → ℝ ∪ {−∞}`
plurisubharmonic. With `U_ε` the set of points of `U` further than `ε > 0` from `∂U`
(Euclidean distance), there is, for every `ε > 0`, a smooth plurisubharmonic
`f_ε : U_ε → ℝ` with `f_ε(z) ≥ f(z)`, and `f(z) = lim_{ε → 0} f_ε(z)` for all `z ∈ U`
(limit as `ε → 0⁺`, in `EReal`, so it covers the points where `f(z) = −∞`). -/
theorem psh_smoothing {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → EReal) (hf : IsPlurisubharmonicOn f U) :
    ∃ F : ℝ → EuclideanSpace ℂ (Fin n) → ℝ,
      (∀ ε : ℝ, 0 < ε →
        ContDiffOn ℝ ∞ (F ε) (awayFromBoundary U ε) ∧
        IsPlurisubharmonicOn (fun z => (F ε z : EReal)) (awayFromBoundary U ε) ∧
        ∀ z ∈ awayFromBoundary U ε, f z ≤ (F ε z : EReal)) ∧
      ∀ z ∈ U, Filter.Tendsto (fun ε => (F ε z : EReal)) (𝓝[>] 0) (𝓝 (f z)) := by sorry

end LeblSCV.Pseudoconvex
