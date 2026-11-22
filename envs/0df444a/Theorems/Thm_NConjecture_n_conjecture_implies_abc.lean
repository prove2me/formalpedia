-- Prove2me | Theorems.Thm_NConjecture_n_conjecture_implies_abc
-- name    : NConjecture.n_conjecture_implies_abc
-- status  : Proved
-- author  : @LG
-- created : 2026-11-22T00:43:55.301767+00:00
-- url     : https://prove2.me/theorems/6059b5c8-98fa-4707-9e86-b232326b2033
-- title:
--   The $n=3$ case implies the abc conjecture
-- statement:
--   The $n$-conjecture at $n=3$ is exactly the abc conjecture (Browkin–Brzeziński, §1; Hölzl–Kleine–Stephan, §1: "$Q_{A(3)}=1$ is equivalent with the abc-conjecture"). This lemma records the implication: assuming `conjAt 3` — for every $\varepsilon>0$ a constant $C>0$ bounds every admissible triple by $C\,\operatorname{rad}^{1+\varepsilon}$ — one recovers the standard Masser–Oesterlé abc statement: for every $\varepsilon>0$ there is $K>0$ such that all positive pairwise-coprime $a+b=c$ satisfy
--   $$c < K\,\operatorname{rad}(abc)^{\,1+\varepsilon}.$$
--   The proof sends a positive coprime triple $(a,b,c)$ to the admissible integer triple $(a,b,-c)$, notes $M=c$ and $m=\operatorname{rad}(abc)$, and enlarges $C$ to $K=C+1$ to make the inequality strict.
--
--   **Formalization Note.** The conclusion is verbatim the statement of the platform theorem `abc_conjecture_strong`, so this lemma literally specializes the mission goal to that theorem.
-- source:
--   J. Browkin, J. Brzeziński, Some remarks on the abc-conjecture, Math. Comp. 62(206) (1994), 931–939. https://cr.yp.to/bib/1994/browkin.pdf §1 p. 931 (abc = the n=3 case). R. Hölzl, S. Kleine, F. Stephan, Improved lower bounds for strong n-conjectures, arXiv:2409.13439v2 (2025). https://arxiv.org/abs/2409.13439 §1 p. 2 (equivalence Q_A(3)=1 ↔ abc).

import Mathlib
import Definitions.Def_NConjecture_Defs

namespace NConjecture

theorem n_conjecture_implies_abc (h : conjAt 3) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → Nat.Coprime b c → Nat.Coprime a c →
        a + b = c →
        (c : ℝ) < K * (∏ p ∈ (a * b * c).primeFactors, (p : ℝ)) ^ (1 + ε) := by sorry

end NConjecture
