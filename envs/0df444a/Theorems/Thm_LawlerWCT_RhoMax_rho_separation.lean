-- Prove2me | Theorems.Thm_LawlerWCT_RhoMax_rho_separation
-- name    : LawlerWCT.RhoMax.rho_separation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:08.674165+00:00
-- url     : https://prove2.me/theorems/7bc02fba-f4bf-44c6-a3f6-97f1e6bc77cb
-- title:
--   §7, p. 16 — two distinct attainable ratios differ by at least 1/(np*)²
-- statement:
--   Let $N$ be a finite set of $n=|N|$ jobs with integer weights $w_j$ and integer processing times satisfying $1\le p_j\le p^*$. Let $I,I'\subseteq N$ be nonempty and suppose their ratios differ, $\rho(I)\neq\rho(I')$. Then
--   $$\bigl|\rho(I)-\rho(I')\bigr|\ge\frac{1}{(n\,p^*)^2}.$$
--
--   This is the resolution of the binary search: once the optimal ratio is known to lie in an interval of length at most $\varepsilon=1/(np^*)^2$, no other attainable ratio fits between the left end and the optimum.
--
--   **Formalization Note.** The printed display ends with "$<\left|1/(np^*)^2\right|$". The sentence that introduces it asks for a value $\varepsilon$ "no greater than the difference between any two distinct attainable ratios", and the arithmetic ($|wp'-w'p|\ge1$ for distinct ratios of integer data, $pp'\le(np^*)^2$) gives $\ge$; the statement uses $\ge$. "Attainable ratio" is read as the ratio of any nonempty subset of $N$, which includes the initial sets; the bounds on $w_j$ are not needed and are omitted, and the precedence digraph does not appear. $n$ and $p^*$ are cast to reals before dividing.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, p. 16, §7, display "| w/p − w'/p' | = | (wp' − w'p)/(pp') | < | 1/(np*)² |"

import Mathlib
import Definitions.Def_LawlerWCT_RhoMax_Model

namespace LawlerWCT.RhoMax

theorem rho_separation {ι : Type*} (N : Finset ι) (w p : ι → ℤ) (pstar : ℤ)
    (hpb : ∀ j ∈ N, 1 ≤ p j ∧ p j ≤ pstar) (I I' : Finset ι) (hI : I ⊆ N) (hI' : I' ⊆ N)
    (hIne : I.Nonempty) (hI'ne : I'.Nonempty)
    (hne : LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I ≠
      LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I') :
    1 / ((N.card : ℝ) * (pstar : ℝ)) ^ 2 ≤
      |LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I -
        LawlerWCT.SeriesPar.rho (fun j => (p j : ℝ)) (fun j => (w j : ℝ)) I'| := by sorry

end LawlerWCT.RhoMax
