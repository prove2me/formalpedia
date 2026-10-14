-- Prove2me | Theorems.Thm_MusicStreaming_CoreSelection_equal_totals
-- name    : MusicStreaming.CoreSelection.equal_totals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:04.46286+00:00
-- url     : https://prove2.me/theorems/78df580d-6272-493b-a542-d316ec0ce740
-- title:
--   Appendix, proof of Theorem 3, p. 25 — any two distinct users have one-user problems with equal index totals
-- statement:
--   Let $I$ be an index on $\mathcal P^*$ satisfying homogeneity, additivity and core selection. Let $j^1 \neq j^2$ be two users with nonzero streaming profiles $x, y \in \mathbb N^N$ such that the one-user problems $(N,\{j^1\},x)$ and $(N,\{j^2\},y)$ lie in $\mathcal P^*$. Then
--   $$
--   \sum_{i' \in N} I_{i'}(N, \{j^1\}, x) = \sum_{i' \in N} I_{i'}(N, \{j^2\}, y).
--   $$
--
--   This removes the disjointness hypothesis of the Claim. It is the step that makes the constant $p = \sum_{i'} I_{i'}(N,\{j\},t_{\cdot j})$ independent of the user and of the profile, from which Theorem 3 follows by additivity.
--
--   **Formalization Note** Users are natural numbers, so the proof may use a third user $j^3 \notin \{j^1, j^2\}$ as the page does; no hypothesis on the number of users is added. Stated for arbitrary nonzero profiles in place of the columns of a problem in $\mathcal P^*$.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 25, Appendix, proof of Theorem 3, display "for each pair j¹, j² ∈ M, with j¹ ≠ j²"

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting

namespace MusicStreaming.CoreSelection

/-- Appendix, proof of Theorem 3, p. 25: any two distinct users have one-user problems (in `𝒫*`)
with the same index total. -/
theorem equal_totals (n : ℕ) (I : MusicStreaming.Axioms.Index n) (hI : IsIndexOn I) (hH : HomogeneityOn I)
    (hA : AdditivityOn I) (hC : CoreSelectionOn I) (j₁ j₂ : ℕ) (x y : Fin n → ℕ)
    (hj : j₁ ≠ j₂) (hx : x ≠ 0) (hy : y ≠ 0)
    (hPx : InPStar (Finsupp.single j₁ x)) (hPy : InPStar (Finsupp.single j₂ y)) :
    ∑ i, I (Finsupp.single j₁ x) i = ∑ i, I (Finsupp.single j₂ y) i := by sorry

end MusicStreaming.CoreSelection
