-- Prove2me | Theorems.Thm_MunkresAlg_Assignment_step2_sequence
-- name    : MunkresAlg.Assignment.step2_sequence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:32:03.559308+00:00
-- url     : https://prove2.me/theorems/b2632078-cc46-41d7-98bf-6c60d6424ea4
-- title:
--   §1, Step 2, first bracket, p. 34 — the alternating sequence Z_0, …, Z_2k exists, is unique, and has distinct elements
-- statement:
--   Let $A$ be a real $n\times n$ matrix and let $s$ be a state reachable by Munkres' algorithm from $A$ that is at Step 2 with the primed zero $Z_0$. Call a list $Z_0,Z_1,\dots,Z_{2k}$ a **Step 2 sequence** if it starts at $Z_0$, each $Z_{2i+1}$ is a starred zero in the column of $Z_{2i}$, each $Z_{2i+2}$ is a primed zero in the row of $Z_{2i+1}$, and $Z_{2k}$ has no starred zero in its column. Then:
--
--   1. a Step 2 sequence exists (the construction never fails and the sequence stops);
--   2. any two Step 2 sequences are equal (the sequence is uniquely specified);
--   3. the elements of a Step 2 sequence are distinct;
--   4. $Z_0$ is a primed zero, it is non-covered, and it is the only non-covered primed zero.
--
--   These facts make Step 2 well defined; part 1 is what rules out the algorithm getting stuck at Step 2.
-- source:
--   Munkres, Algorithms for the assignment and transportation problems, J. SIAM 5 (1957), p. 34, §1, Step 2, first bracket (and '[There is only one.]')

import Mathlib
import Definitions.Def_MunkresAlg_Assignment_Basic
import Definitions.Def_MunkresAlg_Assignment_Algorithm

namespace MunkresAlg.Assignment

/-- §1, Step 2, p. 34: at Step 2 the alternating sequence `Z₀, Z₁, …, Z₂ₖ` exists (it stops),
it is uniquely specified, its elements are distinct, and `Z₀` is the only non-covered primed
zero. -/
theorem step2_sequence {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n)
    (z₀ : Fin n × Fin n) (hs : Reachable A s) (hph : s.phase = Phase.step2 z₀) :
    (∃ zs, IsStep2Seq s z₀ zs) ∧
    (∀ zs zs', IsStep2Seq s z₀ zs → IsStep2Seq s z₀ zs' → zs = zs') ∧
    (∀ zs, IsStep2Seq s z₀ zs → zs.Nodup) ∧
    (z₀ ∈ s.primed ∧ NonCovered s z₀ ∧ ∀ p ∈ s.primed, NonCovered s p → p = z₀) := by sorry

end MunkresAlg.Assignment
