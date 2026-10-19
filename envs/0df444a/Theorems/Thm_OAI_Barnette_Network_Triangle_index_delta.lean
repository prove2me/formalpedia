-- Prove2me | Theorems.Thm_OAI_Barnette_Network_Triangle_index_delta
-- name    : OAI.Barnette.Network.Triangle.index_delta
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:26:02.908561+00:00
-- url     : https://prove2.me/theorems/f2f82afe-428d-4139-94dc-4f4cd2a47679
-- title:
--   Index increments on an oriented face triangle are signed black gradients
-- statement:
--   Let $N$ and $D$ be oriented networks on a common finite edge set $E$: $N$ has vertex set $V$ with tail and head maps $t_N,h_N:E\to V$, and $D$ has vertex set $F$ with $t_D,h_D:E\to F$. For $g:V\to\mathbb{R}$ the gradient is $(\nabla_N g)(e)=g(h_N(e))-g(t_N(e))$. For $e\in E$ and $z\in F$ the arc sign is $\sigma_D(e,z)=1$ if $t_D(e)=z$ and $\sigma_D(e,z)=-1$ otherwise. The star of $v\in V$ is $\operatorname{st}(v)=\{e\in E: t_N(e)=v\text{ or }h_N(e)=v\}$, and $\mathbf 1_S$ denotes the indicator function of a set $S$.
--
--   A triangle of $D$ on an edge set $S\subseteq E$ consists of three distinct corners $c_0,c_1,c_2\in F$ and three distinct edges $e_0,e_1,e_2$ with $\{e_0,e_1,e_2\}=S$, such that for each $i\in\mathbb{Z}/3$ the edge $e_i$ joins $c_i$ and $c_{i+1}$ in $D$ (in one of the two directions). For $i\neq j$ in $\mathbb{Z}/3$ the side $s(i,j)$ is $e_i$ if $j=i+1$ and $e_j$ otherwise; it is the edge joining $c_i$ and $c_j$. The index increment $\delta:\mathbb{Z}/3\times\mathbb{Z}/3\to\{-1,0,1\}$ is given by $\delta(i,i)=0$, $\delta(i,i+1)=1$ and $\delta(i,i-1)=-1$.
--
--   **Theorem.** Let $v\in V$ and let $(c,e)$ be a triangle of $D$ on $\operatorname{st}(v)$ which is oriented, meaning that $(\nabla_N\mathbf 1_{\{v\}})(e_i)=\sigma_D(e_i,c_i)$ for $i=0,1,2$. Let $B\subseteq V$ be a set of black vertices such that every edge has exactly one black endpoint ($t_N(e)\in B$ if and only if $h_N(e)\notin B$), and suppose $v\in B$. Then for all $i\neq j$ in $\mathbb{Z}/3$
--
--   $$\delta(i,j)=(\nabla_N\mathbf 1_B)\big(s(i,j)\big)\cdot\sigma_D\big(s(i,j),c_i\big).$$
--
--   In the intended application $N$ is a properly two-colored cubic network and the triangle on $\operatorname{st}(v)$ is the face triangle of $v$ in the dual network $D$. The identity rewrites the purely combinatorial increment between two corner labels of the face triangle of a black vertex as the black-indicator gradient on the dual edge joining those corners, signed by the direction in which that edge leaves $c_i$. Summing it along a dual cycle that passes through face triangles of black vertices turns a total index increment into the circulation of $\nabla_N\mathbf 1_B$ around the cycle; this is how index sums of incidence-state cycles are evaluated.
--
--   **Formalization Note** The triangle is `t : D.Triangle (N.star v)` with fields `t.corner` and `t.edge`, the side is `t.side D i j`, the increment is the integer-valued `TriangleSystem.indexDelta i j` (cast to the reals), the arc sign is `D.arcSign`, and the black set is a predicate `black` on vertices. Only the edge type is assumed finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/TriangleSystem.lean#L290-L314

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

omit [Fintype V] [Fintype F] in
theorem OAI.Barnette.Network.Triangle.index_delta (v : V) (t : D.Triangle (N.star v))
    (ht : ∀ i, N.gradient (fun w => if w = v then 1 else 0) (t.edge i) =
      D.arcSign (t.edge i) (t.corner i)) (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (hv : black v)
    {i j : Fin 3} (hij : i ≠ j) :
    (Barnette.TriangleSystem.indexDelta i j : ℝ) =
      N.gradient (fun w => if black w then 1 else 0) (t.side D i j) *
        D.arcSign (t.side D i j) (t.corner i) := by sorry
