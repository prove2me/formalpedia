-- Prove2me | Theorems.Thm_LeblSCV_Levi_removable_point
-- name    : LeblSCV.Levi.removable_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T03:07:35.938899+00:00
-- url     : https://prove2.me/theorems/882fa123-b05c-44b6-9030-7728019385e0
-- title:
--   Corollary 2.1.5 — isolated points are removable for holomorphic functions when $n \ge 2$
-- statement:
--   Let $n \ge 2$, let $U \subset \mathbb{C}^n$ be open and $p \in U$. Then every $f \in \mathcal{O}(U \setminus \{p\})$ extends holomorphically to $U$: there is $F \in \mathcal{O}(U)$ with
--   $$F = f \quad \text{on } U \setminus \{p\}.$$
--   This is the simplest instance of the Hartogs phenomenon; it fails for $n = 1$ ($1/z$).
--
--   **Formalization Note.** Holomorphic is `DifferentiableOn ℂ` on open sets; $\mathbb{C}^n$ is `Fin n → ℂ`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 50, Corollary 2.1.5

import Mathlib

namespace LeblSCV.Levi

/-- Corollary 2.1.5 (Lebl, p. 50): for `n ≥ 2`, `U ⊆ ℂⁿ` open and `p ∈ U`, every holomorphic
function on `U ∖ {p}` extends holomorphically to `U`. -/
theorem removable_point {n : ℕ} (hn : 2 ≤ n) (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (p : Fin n → ℂ) (hp : p ∈ U) (f : (Fin n → ℂ) → ℂ) (hf : DifferentiableOn ℂ f (U \ {p})) :
    ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ Set.EqOn F f (U \ {p}) := by sorry

end LeblSCV.Levi
