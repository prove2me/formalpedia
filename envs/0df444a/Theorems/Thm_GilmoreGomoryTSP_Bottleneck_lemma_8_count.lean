-- Prove2me | Theorems.Thm_GilmoreGomoryTSP_Bottleneck_lemma_8_count
-- name    : GilmoreGomoryTSP.Bottleneck.lemma_8_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:56.593018+00:00
-- url     : https://prove2.me/theorems/9fa88a94-53c8-44c6-84c2-185b6d673b31
-- title:
--   Lemma 8 — for fixed q, (22a) and (22b) hold for equally many indices
-- statement:
--   Let $\varphi$ and $\psi$ be permutations of the jobs $1,\dots,N$ and fix an index $q$ with $1 \le q < N$. Then the number of indices $i$ satisfying (22a) equals the number of indices $j$ satisfying (22b):
--   $$\#\{\, i : i \le q < \varphi^{-1}\psi(i) \,\} \;=\; \#\{\, j : \varphi^{-1}\psi(j) \le q < j \,\}.$$
--
--   In words: the permutation $\varphi^{-1}\psi$ sends as many indices from $\{1,\dots,q\}$ above $q$ as it sends from above $q$ into $\{1,\dots,q\}$. This counting fact is used to show that an arc of $G_\psi^*$ outside $G_\varphi$ always comes with an index satisfying (22a).
--
--   **Formalization Note** The statement involves only $\varphi$, $\psi$ and $q$; the ranking property of $\varphi$, which the paper has in force, is not used in it and is not assumed. $q$ ranges over the arc indices `Fin n` (0-based), the range in which (22a)/(22b) are used.
-- source:
--   Gilmore and Gomory, Sequencing a one state-variable machine, Oper. Res. 12 (1964), p. 668, Lemma 8

import Mathlib
import Definitions.Def_GilmoreGomoryTSP_Bottleneck_Model

namespace GilmoreGomoryTSP.Bottleneck

open Classical in
theorem lemma_8_count {n : ℕ} (φ ψ : Equiv.Perm (Fin (n + 1))) (q : Fin n) :
    (Finset.univ.filter (fun i => Cond22a φ ψ q i)).card =
      (Finset.univ.filter (fun j => Cond22b φ ψ q j)).card := by sorry

end GilmoreGomoryTSP.Bottleneck
