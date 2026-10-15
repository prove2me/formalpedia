-- Prove2me | Theorems.Thm_OAI_ParityWL_WeightedWitness_no_tags
-- name    : OAI.ParityWL.WeightedWitness.no_tags
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:42:50.754745+00:00
-- url     : https://prove2.me/theorems/170d033b-b311-4a60-a48c-dd7371340cf4
-- title:
--   A weighted witness rules out every compatible system of parity tags
-- statement:
--   Let $T$ be a graph on a finite set $A$, let $F$ be a graph on a finite set $W$, let $a\colon F\to T$ be a graph homomorphism, and let $b\colon A\to\mathbb{F}_2$. A *weighted witness* $w=(\lambda,\mu)$ for $(T,F,a,b)$ consists of vertex weights $\lambda\colon W\to\mathbb{F}_2$ and edge weights $\mu\colon W\times W\to\mathbb{F}_2$ such that $\mu(x,y)=\mu(y,x)$, $\mu(x,y)=0$ whenever $xy$ is not an edge of $F$, $\sum_{y\in W,\ a(y)=u}\mu(x,y)=\lambda(x)$ for every $x\in W$ and every neighbour $u$ of $a(x)$ in $T$, and $\sum_{x\in W}\lambda(x)\,b(a(x))=1$. A *tag system* assigns to every $x\in W$ a function $z_x\colon N_T(a(x))\to\mathbb{F}_2$ on the neighbourhood of $a(x)$ in $T$.
--
--   **Theorem.** If a weighted witness for $(T,F,a,b)$ exists, then there is no tag system $(z_x)_{x\in W}$ satisfying both
--   $$
--   \sum_{u\in N_T(a(x))}z_x(u)=b(a(x))\quad\text{for all }x\in W\qquad\text{and}\qquad z_x(a(y))=z_y(a(x))\quad\text{for all edges }xy\in E(F).
--   $$
--
--   The two families of equations form the $\mathbb{F}_2$-linear system whose solutions describe how a homomorphism into the base of a parity lift lifts to the lift itself (each vertex chooses a tag of the prescribed parity, and adjacent vertices agree on the shared edge). The theorem is the soundness half of the duality: a weighted witness certifies that this system is inconsistent. The converse, existence of a witness for every inconsistent system, is a separate result.
--
--   **Formalization Note** `WeightedWitness T F a b` has fields `vertex` ($\lambda$), `edge` ($\mu$), `symmetric`, `supported`, `coordinate` and `odd`; `Bit` is `ZMod 2`. The tag system is a dependent function `z : (x : W) → T.neighborSet (a x) → Bit`, and the conclusion of the Lean statement is `False` under the two displayed hypotheses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Witnesses.lean#L65-L85

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {A W : Type} [Fintype A] [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

theorem OAI.ParityWL.WeightedWitness.no_tags (w : WeightedWitness T F a b)
    (z : (x : W) → T.neighborSet (a x) → Bit)
    (hz : ∀ x, ∑ u, z x u = b (a x))
    (he : ∀ x y (h : F.Adj x y),
      z x ⟨a y, a.map_adj h⟩ = z y ⟨a x, a.map_adj h.symm⟩) : False := by sorry
