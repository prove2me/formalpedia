-- Prove2me | Theorems.Thm_LeblSCV_Hartogs_hartogs_phenomenon
-- name    : LeblSCV.Hartogs.hartogs_phenomenon
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T09:11:25.593132+00:00
-- url     : https://prove2.me/theorems/c58f8524-10dc-4f0c-9e96-5c54c797848f
-- title:
--   Theorem 4.3.1 — Hartogs phenomenon
-- statement:
--   Let $n \ge 2$, let $U \subset \mathbb{C}^n$ be a domain (a nonempty connected open set), and let $K \subset U$ be a compact set such that $U \setminus K$ is connected. Then every holomorphic function $f : U \setminus K \to \mathbb{C}$ extends uniquely to a holomorphic function on $U$: there is a holomorphic $F : U \to \mathbb{C}$ with
--   $$F|_{U \setminus K} = f,$$
--   and any holomorphic $G : U \to \mathbb{C}$ with $G|_{U\setminus K} = f$ equals $F$ on $U$.
--
--   Nothing of this kind holds in one variable ($f(z) = 1/z$ on a punctured disc), and the connectedness of $U \setminus K$ cannot be dropped. The theorem shows that holomorphic functions of several variables cannot have compact singularity sets, and is the starting point of the theory of domains of holomorphy.
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ`; functions are total and only their values on the relevant sets enter. Holomorphic is `DifferentiableOn ℂ` on the open sets $U \setminus K$ and $U$, which on open sets is equivalent to the book's Definition 1.1.2 (Proposition 1.1.3, Theorem 1.2.1, Osgood). "$K \subset\subset U$ compact" is `IsCompact K ∧ K ⊆ U`. Uniqueness is stated as agreement on $U$ of any two extensions, since values off $U$ are arbitrary.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 135, Theorem 4.3.1

import Mathlib

namespace LeblSCV.Hartogs

/-- Theorem 4.3.1 (Hartogs phenomenon, Lebl, p. 135). Let `U ⊆ ℂⁿ` be a domain (a connected open
set), `n ≥ 2`, and let `K ⊂⊂ U` be a compact set such that `U \ K` is connected. Every holomorphic
`f : U \ K → ℂ` extends uniquely to a holomorphic function on `U`: there is `F` holomorphic on `U`
with `F = f` on `U \ K`, and every `G` holomorphic on `U` with `G = f` on `U \ K` equals `F` on `U`.
Holomorphic is `DifferentiableOn ℂ` on the open set (equivalent to Definition 1.1.2 there). -/
theorem hartogs_phenomenon {n : ℕ} (hn : 2 ≤ n) {U K : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hUc : IsConnected U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hUK : IsConnected (U \ K)) {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (U \ K)) :
    ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ Set.EqOn F f (U \ K) ∧
      ∀ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G U → Set.EqOn G f (U \ K) →
        Set.EqOn G F U := by sorry

end LeblSCV.Hartogs
