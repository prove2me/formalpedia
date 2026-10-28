-- Prove2me | Theorems.Thm_MusicStreaming_CoreSelection_theorem_3
-- name    : MusicStreaming.CoreSelection.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:50.465776+00:00
-- url     : https://prove2.me/theorems/3b676423-5eeb-413c-b483-14032e31a7da
-- title:
--   Theorem 3, p. 14 — on 𝒫*, homogeneity, additivity and core selection characterize the user-centric index
-- statement:
--   Let $\mathcal P^*$ be the domain of streaming problems in which no user has played content from every artist. Let $I$ be a popularity index on $\mathcal P^*$: for every problem in $\mathcal P^*$ with at least one user, $I(N,M,t) \ge 0$ and $\sum_{i\in N} I_i(N,M,t) > 0$. Then $I$ satisfies
--
--   1. homogeneity,
--   2. additivity, and
--   3. core selection, $R^I(N,M,t) \in C(N, v)$ for the streaming game $v(S) = |\{j\in M: L^j \subseteq S\}|$,
--
--   on $\mathcal P^*$ if and only if it is the user-centric index, that is, there is a constant $c > 0$ such that
--   $$
--   I_i(N,M,t) = c \sum_{j \in M} \frac{t_{ij}}{T^j} \qquad \text{for every } (N,M,t) \in \mathcal P^* \text{ and } i \in N .
--   $$
--
--   Among all ways to measure popularity that are homogeneous and additive, the user-centric rule is therefore the only one whose payments are always stable against coalitions of artists, in the sense of the core.
--
--   **Formalization Note** The paper identifies an index with its positive multiples (p. 8), so "is the user-centric index" is the existence of one global $c > 0$ with $I = c\,U$ on all of $\mathcal P^*$. The index is a function on all problems, but only its values on $\mathcal P^*$ enter the hypotheses and the conclusion. The domain is the reading of $\mathcal P^*$ that the proof uses: the proof applies the axioms to one- and two-user problems "in $\mathcal P^*$" and draws a third user from the population, so $\mathcal P^*$ is every problem in which no user played every artist, and "with at least three users" is a property of the user population, the infinite set $\mathbb N$ of user names. A reading restricting the axioms to problems with at least three users is a different statement that the paper's proof does not cover. Additivity is for disjoint user groups. With one artist, $\mathcal P^*$ contains only the empty problem and the theorem is vacuous, as on the page; no hypothesis on $n$ is added.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 14, Theorem 3 (domain 𝒫* defined on the same page); proof in the Appendix, pp. 23–25

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting

namespace MusicStreaming.CoreSelection

/-- Theorem 3 (arXiv:2310.11861v1, p. 14): in the domain `𝒫*`, an index satisfies homogeneity,
additivity and core selection if and only if it is the user-centric index, i.e. a positive
multiple `c • U` of it on `𝒫*` (indices are identified with their positive multiples, p. 8). -/
theorem theorem_3 (n : ℕ) (I : MusicStreaming.Axioms.Index n) (hI : IsIndexOn I) :
    (HomogeneityOn I ∧ AdditivityOn I ∧ CoreSelectionOn I) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ t : MusicStreaming.Axioms.Problem n, InPStar t → I t = c • userCentric t := by sorry

end MusicStreaming.CoreSelection
