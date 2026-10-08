-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_MinCost_lemma_8_count_22a_22b
-- name    : GilmoreGomoryTSP.MinCost.lemma_8_count_22a_22b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:01:59.848+00:00
-- url     : https://prove2.me/theorems/b2a57674-5b33-45f4-9af2-ec4e5213dd54
-- title:
--   Lemma 8 — (22a) and (22b) hold for equally many indices
-- statement:
--   Let $\varphi,\psi$ be permutations of $\{1,\dots,N\}$ and fix $q\in\{1,\dots,N-1\}$. Then
--   $$\#\{i \mid i\le q<\varphi^{-1}\psi(i)\} = \#\{j \mid \varphi^{-1}\psi(j)\le q<j\}.$$
--   That is, the number of indices $i$ for which (22a) holds equals the number of indices $j$ for which (22b) holds.
--
--   This counting fact makes the $f$- and $g$-contributions of each interval $P_q$ to $c^*(\psi)$ pair up into multiples of $\|P_q\|$.
--
--   **Formalization Note** In 0-based indexing $q$ is `q : Fin n` and the comparisons are with `q.castSucc`; the statement is purely combinatorial and holds for any $\varphi,\psi$.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 668, Lemma 8

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_MinCost_Model
import Definitions.Def_GilmoreGomoryTSP_MinCost_Underestimate

namespace GilmoreGomoryTSP.MinCost

theorem lemma_8_count_22a_22b {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) :
    (Finset.univ.filter fun i => i ≤ q.castSucc ∧ q.castSucc < φ.symm (ψ i)).card =
      (Finset.univ.filter fun j => φ.symm (ψ j) ≤ q.castSucc ∧ q.castSucc < j).card := by sorry

end GilmoreGomoryTSP.MinCost
