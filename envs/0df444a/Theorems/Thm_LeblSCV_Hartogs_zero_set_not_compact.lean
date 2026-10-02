-- Prove2me | Theorems.Thm_LeblSCV_Hartogs_zero_set_not_compact
-- name    : LeblSCV.Hartogs.zero_set_not_compact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T09:20:31.817983+00:00
-- url     : https://prove2.me/theorems/7026b029-1c8d-4356-867d-57477895d2a3
-- title:
--   Corollary 4.3.2 — zero sets are never compact in dimension ≥ 2
-- statement:
--   Let $n \ge 2$, let $U \subset \mathbb{C}^n$ be a domain (a nonempty connected open set), and let $f : U \to \mathbb{C}$ be holomorphic. If the zero set
--   $$f^{-1}(0) = \{ z \in U : f(z) = 0 \}$$
--   is not empty, then it is not compact.
--
--   In one variable zeros are isolated, so this fails for $n = 1$; in several variables it is a consequence of the Hartogs phenomenon (Theorem 4.3.1) applied to $1/f$.
--
--   **Formalization Note.** Holomorphic is `DifferentiableOn ℂ f U` on the open set $U$ (equivalent to Definition 1.1.2 there). The zero set is taken inside $U$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 136, Corollary 4.3.2

import Mathlib

namespace LeblSCV.Hartogs

/-- Corollary 4.3.2 (Lebl, p. 136). Let `U ⊆ ℂⁿ`, `n ≥ 2`, be a domain (a connected open set) and
`f : U → ℂ` holomorphic. If the zero set `f⁻¹(0) = {z ∈ U : f(z) = 0}` is not empty, then it is not
compact. Holomorphic is `DifferentiableOn ℂ` on the open set. -/
theorem zero_set_not_compact {n : ℕ} (hn : 2 ≤ n) {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hUc : IsConnected U) {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U)
    (hne : {z | z ∈ U ∧ f z = 0}.Nonempty) :
    ¬ IsCompact {z | z ∈ U ∧ f z = 0} := by sorry

end LeblSCV.Hartogs
