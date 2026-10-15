-- Prove2me | Theorems.Thm_OAI_ParityWL_inconsistent_weightedWitness
-- name    : OAI.ParityWL.inconsistent_weightedWitness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:36:40.660219+00:00
-- url     : https://prove2.me/theorems/8e1642bc-3cd6-4df5-9f1a-e57f8378688e
-- title:
--   An inconsistent projected lift system yields a symmetric edge-weighted dual witness
-- statement:
--   Let $T$ be a simple graph on a finite set $A$, let $G$ be a simple graph on a set $V$, let $F$ be a simple graph on a finite set $W$, let $\tau:G\to T$ and $\varphi:F\to G$ be graph homomorphisms, and let $b:A\to\mathbb{F}_2$, where $\mathbb{F}_2=\mathbb{Z}/2\mathbb{Z}$. Suppose the projected lift system $\mathcal S_\varphi(b)$ has no solution, that is, there is no family $z=(z_x)_{x\in W}$ of functions $z_x:N_T(\tau\varphi(x))\to\mathbb{F}_2$ with $\sum_{c\in N_T(\tau\varphi(x))}z_x(c)=b(\tau\varphi(x))$ for all $x\in W$ and $z_x(\tau\varphi(y))=z_y(\tau\varphi(x))$ for all edges $xy$ of $F$.
--
--   Then there is a weighted witness for the composite homomorphism $a=\tau\circ\varphi:F\to T$ and $b$: a vertex weight $\omega:W\to\mathbb{F}_2$ and an edge weight $\varepsilon:W\times W\to\mathbb{F}_2$ such that $\varepsilon(x,y)=\varepsilon(y,x)$ for all $x,y\in W$, $\varepsilon(x,y)=0$ whenever $xy\notin E(F)$, and
--   $$
--   \sum_{y\in W,\ a(y)=c}\varepsilon(x,y)=\omega(x)\quad\text{for all }x\in W\text{ and all }c\in N_T(a(x)),\qquad\sum_{x\in W}\omega(x)\,b(a(x))=1 .
--   $$
--
--   A weighted witness certifies inconsistency using only the type map $a=\tau\circ\varphi$ into the template, not the graph $G$; a companion result shows conversely that a weighted witness excludes every solution. In the parity reduction, a strict homomorphism-count gap between the star lift and the zero lift gives an inconsistent projected system and hence, by this theorem, a weighted witness, whose masses are then analysed along a tree decomposition of $F$.
--
--   **Formalization Note** The witness is the structure `WeightedWitness T F (τ.comp φ) b` with fields `vertex`, `edge`, `symmetric`, `supported`, `coordinate` and `odd`, and the conclusion is that this type is nonempty. The hypothesis is that `Solutions T G F τ φ b` is empty. Finiteness of $V$ is not assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/WeightedDual.lean#L162-L177

import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual

open OAI OAI.ParityWL
open scoped BigOperators
open scoped Classical
variable {A V W : Type} [Fintype A] [Fintype V] [Fintype W]
variable (T : SimpleGraph A) (G : SimpleGraph V) (F : SimpleGraph W)
variable (τ : G →g T) (φ : F →g G)

omit [Fintype V] in
theorem OAI.ParityWL.inconsistent_weightedWitness (b : A → Bit)
    (h : ¬ Nonempty (Solutions T G F τ φ b)) :
    Nonempty (WeightedWitness T F (τ.comp φ) b) := by sorry
