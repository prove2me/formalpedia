-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_walking_a_unit
-- name    : KawasakiSOS.Threshold.walking_a_unit
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:02:34.570238+00:00
-- url     : https://prove2.me/theorems/923288f4-d384-43a6-81ba-0e1996ec579e
-- title:
--   Lemma 2.2: walking a unit
-- statement:
--   Let $z\in\Omega_{n,k}$ with $z(i)\ge1$, let $j\ne i$, and let $z'=z-e_i+e_j$. Moving the unit step by step along a shorter arc from $i$ to $j$ gives a path of single moves from $z$ to $z'$, of length at most $k/2$, through the states $z-e_i+e_l$, and every such state satisfies
--
--   $$M(z-e_i+e_l)\le M(z-e_i)+2\le\min\{M(z),M(z')\}+2.$$
--
--   This lemma turns a long-range move, called a teleport, into a genuine path of the chain, at an additive cost of $2$ in energy and a factor $k/2$ in length.
--
--   Differences from the source:
--   - reading: "the shorter arc from i to j" → an arc of length at most k/2, either one when i and j are antipodal; reason: the shorter arc is not unique for antipodal columns; the statement covers both choices
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 2.2, p. 6 (PDF p. 7)

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Paths
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_energy
import Definitions.Def_KawasakiSOS_Threshold_transfer
import Definitions.Def_KawasakiSOS_Threshold_removeUnit
import Definitions.Def_KawasakiSOS_Threshold_IsMove
import Definitions.Def_KawasakiSOS_Threshold_IsTeleportWalk
open MarkovMixing DiaconisStroock.Poincare

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Lemma 2.2, p. 6 (PDF p. 7).

Formalization Notes:
- reading: "the shorter arc from i to j" → an arc of length at most k/2, either one when i and j are antipodal. The shorter arc is not unique for antipodal columns; the statement covers both choices. -/
theorem walking_a_unit {n k : ℕ} [NeZero k] (hk : 2 ≤ k) (hkn : k ≤ n) (z : Config n k) (i j : ZMod k) (hi : 1 ≤ z.1 i) (hij : j ≠ i) :
    (∃ l, IsTeleportWalk z i j l) ∧
      ∀ l, IsTeleportWalk z i j l →
        l.head? = some z ∧ l.getLast? = some (transfer z i j) ∧ l.IsChain IsMove ∧
          2 * (pathEdges l).length ≤ k ∧
          (∀ g ∈ l, energy g.1 ≤ energy (removeUnit z.1 i) + 2) ∧
          energy (removeUnit z.1 i) + 2 ≤ min (energy z.1) (energy (transfer z i j).1) + 2 := by sorry

end KawasakiSOS.Threshold
