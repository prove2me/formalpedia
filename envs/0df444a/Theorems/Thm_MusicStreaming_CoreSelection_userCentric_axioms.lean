-- Prove2me | Theorems.Thm_MusicStreaming_CoreSelection_userCentric_axioms
-- name    : MusicStreaming.CoreSelection.userCentric_axioms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:56.20393+00:00
-- url     : https://prove2.me/theorems/c19698a4-6756-422b-8220-ecbd54f5df7d
-- title:
--   Appendix, proof of Theorem 3, p. 23 — the user-centric index satisfies homogeneity, additivity and core selection on 𝒫*
-- statement:
--   On the domain $\mathcal P^*$ of problems in which no user has played every artist, the user-centric index
--   $$
--   U_i(N,M,t) = \sum_{j\in M} \frac{t_{ij}}{T^j}
--   $$
--   satisfies the three axioms of Theorem 3:
--
--   1. **homogeneity**: if $\lambda \ge 0$ and $t_{ij} = \lambda t_{i'j}$ for all $j \in M$, then $U_i = \lambda U_{i'}$;
--   2. **additivity**: for disjoint user groups, $U(N, M^1 \cup M^2, t) = U(N,M^1,t^1) + U(N,M^2,t^2)$;
--   3. **core selection**: $R^U(N,M,t) \in C(N,v)$.
--
--   This is the "if" direction of Theorem 3 for the index $U$ itself; for a positive multiple $cU$ it follows because the rewards do not change under rescaling.
--
--   **Formalization Note** The axioms are quantified over $\mathcal P^*$, read as the proof of Theorem 3 uses it (see the setting module): every problem in which no user played every artist. Additivity is for disjoint user groups.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 23, Appendix, proof of Theorem 3, first sentence

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting

namespace MusicStreaming.CoreSelection

/-- Appendix, proof of Theorem 3, p. 23: the user-centric index satisfies homogeneity,
additivity and core selection (on `𝒫*`). -/
theorem userCentric_axioms (n : ℕ) :
    HomogeneityOn (userCentric (n := n)) ∧ AdditivityOn (userCentric (n := n)) ∧
      CoreSelectionOn (userCentric (n := n)) := by sorry

end MusicStreaming.CoreSelection
