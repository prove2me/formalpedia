-- Prove2me | Theorems.Thm_OAI_Release075_retained_girth
-- name    : OAI.Release075.retained_girth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:44:54.305538+00:00
-- url     : https://prove2.me/theorems/a3a8114c-329b-4cf8-8b11-51a6429835dd
-- title:
--   Deleting short-cycle marks gives girth greater than twelve
-- statement:
--   For marks $a\in V$ in a vector space over a field $K$ and a projective direction $d$ with chosen representative $\hat d$, the point $z$ is punctured-incident to the line $(a,d)$ when $z\ne a$ and $z=a+t\hat d$ for some $t\in K$. For a finite field $K$, a finite $K$-space $V$, marks $S\subseteq V$ and directions $\omega:S\to\mathbb P(V)$, delete every mark lying on an occurring cycle candidate of length $2,\dots,6$. Consider the bipartite incidence graph between points of $V$ and retained marks. Every cycle in it has length
--   $$
--   >12 .
--   $$
--
--   This holds even when distinct labels give the same geometric line.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L554-L575

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

theorem OAI.Release075.retained_girth (S : Finset V) (ω : S → Projectivization K V)
    (a : V ⊕ Retained S ω)
    (w : (relationGraph (fun z (i : Retained S ω) =>
      PuncturedIncidence i.val.val z (ω i.val))).Walk a a) (hw : w.IsCycle) : 12 < w.length := by sorry
