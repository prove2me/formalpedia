-- Prove2me | Theorems.Thm_MildHamilton_Main_claim_2
-- name    : MildHamilton.Main.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:50:55.0382+00:00
-- url     : https://prove2.me/theorems/6f964cde-a3ae-4ba2-b234-c1f9cb5d95c0
-- title:
--   Claim 2 (in the proof of Lemma 4.5), p. 9 — a pairing with both unions acyclic
-- statement:
--   Let $k=2r\ge6$ and let $C=c_0c_1\cdots c_{k-1}c_0$ be a $k$-cycle. Put $A=\{c_0,c_2\}$ and $B=\{c_1,c_4\}$, and let $M_0$ be the perfect matching of $C$ containing $c_0c_1$ and $M_1$ the other one, containing $c_1c_2$. There exists a perfect matching $P$ of $V(C)\setminus(A\cup B)$ such that $M_0\cup P$ and $M_1\cup P$ are both acyclic.
--
--   This pairing is what makes a subdivided even cycle a comparator in Lemma 4.5.
--
--   Differences from the source:
--   - reading: M_0 is "the perfect matching of C matching c_0 to c_2" → M_0 is the perfect matching of C containing c_0c_1; reason: c_0 and c_2 are not adjacent on C, and the next paragraph of the proof uses a c_0–c_1 path in M_0 ∪ P
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Claim 2, in the proof of Lemma 4.5, p. 9

import Mathlib
import Definitions.Def_MildHamilton_Main_Router

namespace MildHamilton.Main

/-- Claim 2, in the proof of Lemma 4.5 (Muyesser, STOC 2027 submission #233, p. 9): for `k = 2r ≥ 6`,
`A = {c_0, c_2}`, `B = {c_1, c_4}`, a perfect matching `P` of `V(C) \ (A ∪ B)` with `M_0 ∪ P` and `M_1 ∪ P`
both acyclic. The cycle vertices are the labels `Fin k`. -/
theorem claim_2 (k : ℕ) [NeZero k] (hk : Even k) (h6 : 6 ≤ k) :
    ∃ P : Finset (Fin k × Fin k),
      IsCyclePairing ({0, 2} : Finset (Fin k)) ({1, 4} : Finset (Fin k)) P ∧
      (matchingM0 k ⊔ pairGraph P).IsAcyclic ∧ (matchingM1 k ⊔ pairGraph P).IsAcyclic := by sorry

end MildHamilton.Main
