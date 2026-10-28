-- Prove2me | Theorems.Thm_MusicStreaming_CoreSelection_one_user_vanish
-- name    : MusicStreaming.CoreSelection.one_user_vanish
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:34.003223+00:00
-- url     : https://prove2.me/theorems/05147156-cb92-48f6-bcbf-5c20c7ef1534
-- title:
--   Appendix, proof of Theorem 3, pp. 23–24, display (1) — on a one-user problem the index vanishes off L^j
-- statement:
--   Let $I$ be an index on $\mathcal P^*$ (nonnegative, with positive total on nonempty problems) that satisfies core selection. Let $j$ be a user with a nonzero streaming profile $x \in \mathbb N^N$ such that the one-user problem $(N, \{j\}, x)$ lies in $\mathcal P^*$, i.e. $L^j = \{i : x_i > 0\} \neq N$. Then
--   $$
--   I_i(N, \{j\}, x) = 0 \quad \text{for each } i \in N \setminus L^j(N, \{j\}, x).
--   $$
--
--   This is display (1) of the proof of Theorem 3: core selection, applied to the coalition $S = L^j$ whose worth is $1$, forces the index of a single user to put all its weight on the artists that user played.
--
--   **Formalization Note** The page states (1) for the column $t_{\cdot j}$ of a user $j$ of a given problem in $\mathcal P^*$; it is stated here for an arbitrary nonzero profile $x$, which is the same statement since every such column is a nonzero profile with $L^j \neq N$, and conversely. The page's "$L^j(N,\{j\},x)$" in the intermediate sums means $L^j(N,\{j\},t_{\cdot j})$.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, pp. 23–24, Appendix, proof of Theorem 3, display (1)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting

namespace MusicStreaming.CoreSelection

/-- Appendix, proof of Theorem 3, pp. 23–24, display (1): under core selection, the index of a
one-user problem `(N, {j}, x)` in `𝒫*` vanishes on every artist the user has not played. -/
theorem one_user_vanish (n : ℕ) (I : MusicStreaming.Axioms.Index n) (hI : IsIndexOn I) (hC : CoreSelectionOn I)
    (j : ℕ) (x : Fin n → ℕ) (hx : x ≠ 0) (hP : InPStar (Finsupp.single j x))
    (i : Fin n) (hi : x i = 0) :
    I (Finsupp.single j x) i = 0 := by sorry

end MusicStreaming.CoreSelection
