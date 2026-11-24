-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_Supplement_theorem_12
-- name    : Gomory69.Asymptotic.Supplement.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:25:39.967376+00:00
-- url     : https://prove2.me/theorems/6fd8542b-53ed-4674-8701-abbcb869dfb3
-- title:
--   THEOREM 12 — Coordinate sections (corrected: restore the zero solution)
-- statement:
--   Let $G$ be a finite Abelian group, $N\subseteq G\setminus\{0\}$, and $g_0\in G$. Write $P_c(G,N,g_0)$ for the published ordinary corner hull, $P_m(G,g_0)$ for the published master hull excluding the zero solution at target zero, $j_N$ for zero extension and $E(N)$ for its coordinate subspace. The full-domain corrected relation is
--   $$j_N(P_c(G,N,g_0))=\operatorname{conv}_{\mathbb R}\bigl((P_m(G,g_0)\cap E(N))\cup Z_{g_0}\bigr),\qquad Z_{g_0}=\begin{cases}\{0\}&g_0=0,\\\varnothing&g_0\ne0.\end{cases}$$
--   At nonzero target this is the printed equality, since the section is convex. At zero target the convex hull with the origin is essential. For $G=\mathbb Z/2$, $N=\{1\}$, the printed sides are $[0,\infty)$ and $[2,\infty)$; their discrepancy is retained in DISPROOF.md.
--
--   This identifies coordinate sections while preserving both immutable definitions and all target cases.
--
--   Differences from the source:
--   - correction: the ordinary corner hull equals the master coordinate section at every target → take the convex hull of the section together with the origin exactly at target zero; reason: the p. 474 footnote removes the zero solution only from the master hull; the p. 475 proof otherwise identifies the nonzero generators
--   - encoding: corner and master spaces are identified → the left-hand set is the image under zeroExtend; reason: the two coordinate types differ; zero extension is exactly the embedding on p. 475
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), DOI 10.1016/0024-3795(69)90017-2, p. 475, THEOREM 12

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_Supplement_CoordinateSection

namespace Gomory69.Asymptotic.Supplement

/-- Full-domain correction: the ordinary corner hull also contains the origin at target zero. -/
theorem theorem_12 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (N : Finset G) (hN : 0 ∉ N) (g₀ : G) :
    zeroExtend N '' groupPolyhedron N g₀ =
      convexHull ℝ ((Gomory69.Lifting.P G g₀ ∩ coordinateSpace N) ∪
        (if g₀ = 0 then {0} else ∅)) := by sorry

end Gomory69.Asymptotic.Supplement
