-- Prove2me | Theorems.Thm_MusicStreaming_Axioms_userCentric_axioms
-- name    : MusicStreaming.Axioms.userCentric_axioms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:25.141987+00:00
-- url     : https://prove2.me/theorems/e4511b3a-59f2-4f54-ba5b-5c175c19f421
-- title:
--   Appendix, proof of Theorem 1(c), p. 20 — Σᵢ Uᵢ(N, M∖{j}, t₋ⱼ) = m − 1; user-centric satisfies homogeneity, additivity and equal global impact
-- statement:
--   Let $U_i(N,M,t)=\sum_{j\in M}t_{ij}/T^j$ be the user-centric index, and $m=|M|$.
--
--   1. For every problem and every user $j\in M$,
--   $$\sum_{i\in N}U_i(N,M\setminus\{j\},t_{-j})=\sum_{k\in M\setminus\{j\}}\sum_{i\in N}\frac{t_{ik}}{T^k}=m-1 .$$
--   2. The user-centric index satisfies homogeneity, additivity and equal global impact of users.
--
--   Since $m-1$ does not depend on $j$, item 1 gives equal global impact; this is the "if" direction of Theorem 1(c).
--
--   **Formalization Note** $m-1$ is real subtraction; it is never applied with $m=0$, since $j\in M$.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 20, Appendix, proof of Theorem 1(c) (labelled "(3)"), first paragraph

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting

namespace MusicStreaming.Axioms

theorem userCentric_axioms {n : ℕ} :
    (∀ (t : Problem n) (j : ℕ), j ∈ t.support →
        ∑ i, userCentric (t.erase j) i = (t.support.card : ℝ) - 1) ∧
      Homogeneity (userCentric (n := n)) ∧ Additivity (userCentric (n := n)) ∧
      EqualGlobalImpact (userCentric (n := n)) := by sorry

end MusicStreaming.Axioms
