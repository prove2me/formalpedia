-- Prove2me | Theorems.Thm_MusicStreaming_CoreSelection_claim
-- name    : MusicStreaming.CoreSelection.claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:42.411153+00:00
-- url     : https://prove2.me/theorems/cb5b2fa1-1f50-41d3-9f24-4cc3cb11d128
-- title:
--   Appendix, proof of Theorem 3, p. 24, Claim — users with disjoint lists have one-user problems with equal index totals
-- statement:
--   Let $I$ be an index on $\mathcal P^*$ satisfying homogeneity, additivity and core selection. Let $j^1 \neq j^2$ be two users with nonzero streaming profiles $x, y \in \mathbb N^N$ such that the one-user problems $(N,\{j^1\},x)$ and $(N,\{j^2\},y)$ lie in $\mathcal P^*$ and the lists of artists they played are disjoint, $L^{j^1}(N,\{j^1\},x) \cap L^{j^2}(N,\{j^2\},y) = \emptyset$. Then
--   $$
--   \sum_{i' \in N} I_{i'}(N, \{j^1\}, x) = \sum_{i' \in N} I_{i'}(N, \{j^2\}, y).
--   $$
--
--   This is the Claim of the proof of Theorem 3. It compares two users through the two-user problem they form, where core selection applied to the coalition $L^{j^1}$ (worth $1$ out of a total of $2$) forbids either user from carrying more weight.
--
--   **Formalization Note** The page states the Claim for two columns $t_{\cdot j^1}, t_{\cdot j^2}$ of a problem in $\mathcal P^*$; it is stated here for arbitrary nonzero profiles $x, y$ of two distinct users, which is the same statement because any two such columns form a problem in $\mathcal P^*$. The hypotheses list all three axioms, as on the page ("let $I$ be an index satisfying the axioms").
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 24, Appendix, proof of Theorem 3, Claim

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting

namespace MusicStreaming.CoreSelection

/-- Appendix, proof of Theorem 3, p. 24, the Claim: two distinct users whose lists of artists are
disjoint have one-user problems with the same index total. -/
theorem claim (n : ℕ) (I : MusicStreaming.Axioms.Index n) (hI : IsIndexOn I) (hH : HomogeneityOn I)
    (hA : AdditivityOn I) (hC : CoreSelectionOn I) (j₁ j₂ : ℕ) (x y : Fin n → ℕ)
    (hj : j₁ ≠ j₂) (hx : x ≠ 0) (hy : y ≠ 0)
    (hPx : InPStar (Finsupp.single j₁ x)) (hPy : InPStar (Finsupp.single j₂ y))
    (hdisj : Disjoint (Finset.univ.filter (fun i => 0 < x i))
      (Finset.univ.filter (fun i => 0 < y i))) :
    ∑ i, I (Finsupp.single j₁ x) i = ∑ i, I (Finsupp.single j₂ y) i := by sorry

end MusicStreaming.CoreSelection
