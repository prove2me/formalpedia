-- Prove2me | Theorems.Thm_MusicStreaming_CoreSelection_one_user_form
-- name    : MusicStreaming.CoreSelection.one_user_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:33.781983+00:00
-- url     : https://prove2.me/theorems/fee7cb0d-966c-49c4-9e92-edf6c048e312
-- title:
--   Appendix, proof of Theorem 3, p. 24 — on a one-user problem, I_i = [Σ_{i′} I_{i′}] U_i
-- statement:
--   Let $I$ be an index on $\mathcal P^*$ satisfying homogeneity and core selection. Let $j$ be a user with a nonzero streaming profile $x \in \mathbb N^N$ such that the one-user problem $(N,\{j\},x)$ lies in $\mathcal P^*$. Then for every artist $i$,
--   $$
--   I_i(N, \{j\}, x) = \Big[ \sum_{i' \in N} I_{i'}(N, \{j\}, x) \Big] \frac{x_i}{\sum_{i' \in N} x_{i'}} = \Big[ \sum_{i' \in N} I_{i'}(N, \{j\}, x) \Big]\, U_i(N, \{j\}, x).
--   $$
--
--   So on a one-user problem the index is the user-centric index scaled by its own total; the remaining step of the proof shows that this total does not depend on the user or the profile.
--
--   **Formalization Note** Stated for an arbitrary nonzero profile $x$ in place of the column $t_{\cdot j}$ of a problem in $\mathcal P^*$, which is the same statement.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 24, Appendix, proof of Theorem 3, display "Hence, I_i(N,{j},t.j) = [Σ_{i′∈N} I_{i′}(N,{j},t.j)] U_i(N,{j},t.j)"

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting

namespace MusicStreaming.CoreSelection

/-- Appendix, proof of Theorem 3, p. 24: on a one-user problem `(N, {j}, x)` in `𝒫*`,
`I_i = [∑_{i'} I_{i'}] · U_i`. -/
theorem one_user_form (n : ℕ) (I : MusicStreaming.Axioms.Index n) (hI : IsIndexOn I) (hH : HomogeneityOn I)
    (hC : CoreSelectionOn I) (j : ℕ) (x : Fin n → ℕ) (hx : x ≠ 0)
    (hP : InPStar (Finsupp.single j x)) (i : Fin n) :
    I (Finsupp.single j x) i =
      (∑ i', I (Finsupp.single j x) i') * userCentric (Finsupp.single j x) i := by sorry

end MusicStreaming.CoreSelection
