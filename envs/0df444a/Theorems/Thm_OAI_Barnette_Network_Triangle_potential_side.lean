-- Prove2me | Theorems.Thm_OAI_Barnette_Network_Triangle_potential_side
-- name    : OAI.Barnette.Network.Triangle.potential_side
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:25:31.667168+00:00
-- url     : https://prove2.me/theorems/d7d63840-8517-438a-a098-5e325d8b6e0b
-- title:
--   Corner potential of a triangle carrying an edge flow with zero circulation
-- statement:
--   Let $D$ be a network with vertex set $F$ and edge set $E$, each edge $e$ having a tail $t_D(e)$ and a head $h_D(e)$ in $F$. For an edge $e$ and a vertex $c$ put $\sigma_D(e,c)=1$ if $t_D(e)=c$ and $\sigma_D(e,c)=-1$ otherwise; thus for an edge joining $c$ to another vertex, $\sigma_D(e,c)$ is the sign of $e$ when it is traversed starting from $c$. Let $T$ be a triangle of $D$: distinct corners $c_0,c_1,c_2\in F$ and distinct edges $e_0,e_1,e_2$ such that $e_i$ joins $c_i$ and $c_{i+1}$ (indices mod $3$). For distinct $i,j\in\mathbb{Z}/3$ let $\operatorname{side}(i,j)$ be $e_i$ if $j=i+1$ and $e_j$ otherwise; this is the edge of $T$ joining $c_i$ and $c_j$.
--
--   Given $\alpha:E\to\mathbb{R}$, let $a_i=\alpha(e_i)\,\sigma_D(e_i,c_i)$ be the flow of $\alpha$ along $e_i$ in the direction from $c_i$ to $c_{i+1}$, and define the corner potential
--   $$
--   p_0=0,\qquad p_1=a_0,\qquad p_2=a_0+a_1 .
--   $$
--   If the circulation of $\alpha$ around $T$ vanishes, $a_0+a_1+a_2=0$, then for all distinct $i,j\in\mathbb{Z}/3$
--
--   $$
--   p_j-p_i=\alpha(\operatorname{side}(i,j))\;\sigma_D\bigl(\operatorname{side}(i,j),c_i\bigr).
--   $$
--
--   So $p$ is a potential for $\alpha$ on the triangle: the potential difference from $c_i$ to $c_j$ equals the flow of $\alpha$ along the side from $c_i$ to $c_j$, in either direction. Such potentials serve as corner weights on the black triangles of a coloured dual, so that the integral of a flow along a cycle built from triangle sides becomes a sum of corner-weight differences.
--
--   **Formalization Note** The potential is `t.potential D α`, a vector indexed by `Fin 3` written with the `![...]` notation, and $\operatorname{side}(i,j)$ is `t.side D i j`; $\sigma_D$ is `D.arcSign`. No finiteness or simplicity assumptions are needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/TriangleSystem.lean#L252-L273

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] [Fintype F] in
theorem OAI.Barnette.Network.Triangle.potential_side {s : Finset E} (t : D.Triangle s) (α : E → ℝ)
    (hα : ∑ i, α (t.edge i) * D.arcSign (t.edge i) (t.corner i) = 0)
    {i j : Fin 3} (hij : i ≠ j) :
    t.potential D α j - t.potential D α i =
      α (t.side D i j) * D.arcSign (t.side D i j) (t.corner i) := by sorry
