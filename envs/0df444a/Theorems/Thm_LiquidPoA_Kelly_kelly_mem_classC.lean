-- Prove2me | Theorems.Thm_LiquidPoA_Kelly_kelly_mem_classC
-- name    : LiquidPoA.Kelly.kelly_mem_classC
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:58.136639+00:00
-- url     : https://prove2.me/theorems/fc2c4d93-5212-46c9-a3eb-0c68374bf244
-- title:
--   p. 14 — the Kelly mechanism belongs to class C
-- statement:
--   For every number $n$ of users, the Kelly mechanism, which allocates $g^{Kelly}_i(s)=s_i/\sum_j s_j$ and charges $p^{Kelly}_i(s)=s_i$, is a resource allocation mechanism in the sense of §2 (including footnote 5) and belongs to the class $\mathcal C$:
--
--   $$
--   \text{Kelly}_n\ \text{satisfies the §2 axioms},\qquad \text{Kelly}_n\in\mathcal C.
--   $$
--
--   Membership in $\mathcal C$ makes Lemma 4.3 applicable to Kelly, which gives the equality case of Lemma 4.2. Only the Kelly part of the paper's observation is stated; SH and E2-PYS are outside this mission.
--
--   **Formalization Note** Kelly's payment is $p_i(s)=s_i$ at every profile, including profiles with fewer than two positive entries. Class $\mathcal C$ is read in each user's own signal, as the proof of Lemma 4.3 uses it.
-- source:
--   Caragiannis, Voudouris, The efficiency of resource allocation mechanisms for budget-constrained users, arXiv:1707.03551v3, pp. 4–5, mechanism properties; p. 14, class C observation

import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

/-- The Kelly part of the class-`𝒞` observation on p. 14, with Section 2's mechanism properties. -/
theorem kelly_mem_classC (n : ℕ) :
    IsRAMechanism (kelly n) ∧ InClassC (kelly n) := by sorry

end LiquidPoA.Kelly
