-- Prove2me | Theorems.Thm_KarpPapadimitriou_Facial_notMem_DLang_iff_lt_on_hull
-- name    : KarpPapadimitriou.Facial.notMem_DLang_iff_lt_on_hull
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:28:46.40427+00:00
-- url     : https://prove2.me/theorems/da52fb89-c191-44b6-ad43-8efb0d3dbab6
-- title:
--   p. 7, proof of Theorem 1, (i)⇔(ii) — ⟨z,c,k⟩ ∉ D(C) iff c·x < k on all of CH(S(z))
-- statement:
--   Let $C$ be a combinatorial optimization problem, $z\in L$, $c\in\mathbb Z^{n(z)}$ and $k\in\mathbb Z$. Then the following are equivalent:
--
--   1. $\langle z,c,k\rangle\notin D(C)$;
--   2. the program $\max\ c\cdot x$ subject to $x\in\mathrm{CH}(S(z))$ has optimal value $<k$, read as
--   $$c\cdot x<k\quad\text{for every }x\in\mathrm{CH}(S(z))\subseteq\mathbb Q^{n(z)}.$$
--
--   This is the first step of the proof of Theorem 1: it replaces the combinatorial question by a statement about the convex hull, to which linear programming applies.
--
--   **Formalization Note** "Has optimal value $<k$" is read as "every feasible point has value $<k$"; this reading is meaningful also when $S(z)$ is empty (vacuously true) and when the objective is unbounded (false), and under it the equivalence holds for every $S(z)$. The triple $\langle z,c,k\rangle$ is its code over $\{0,1,-,\#\}$.
-- source:
--   Karp & Papadimitriou, On linear characterizations of combinatorial optimization problems, MIT/LCS/TM-154 (Feb. 1980), pp. 7–8, proof of Theorem 1, (i)⇔(ii)

import Mathlib
import Definitions.Def_KarpPapadimitriou_Facial_FacialDescription

namespace KarpPapadimitriou.Facial

theorem notMem_DLang_iff_lt_on_hull (C : COP) (z : List Bool) (hz : z ∈ C.L)
    (c : Fin (C.n z) → ℤ) (k : ℤ) :
    encTriple z c k ∉ DLang C ↔
      ∀ x ∈ hull C z, (fun j => (c j : ℚ)) ⬝ᵥ x < (k : ℚ) := by sorry

end KarpPapadimitriou.Facial
