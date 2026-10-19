-- Prove2me | Theorems.Thm_OAI_Barnette_Network_oriented_face
-- name    : OAI.Barnette.Network.oriented_face
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:20:20.657597+00:00
-- url     : https://prove2.me/theorems/e3528b3a-39b9-45b4-b581-ca76c3fb8264
-- title:
--   Coherent orientation of the dual triangle around a vertex
-- statement:
--   Let $N$ and $D$ be networks on a common finite edge set $E$ with vertex sets $V$ and $F$; every edge $e$ has a tail and a head, $t_N(e),h_N(e)\in V$ in $N$ and $t_D(e),h_D(e)\in F$ in $D$. Write $\nabla_N f(e)=f(h_N(e))-f(t_N(e))$ and $\partial_N x(v)=\sum_{e:\,h_N(e)=v}x(e)-\sum_{e:\,t_N(e)=v}x(e)$, similarly for $D$, and let $G(N)$, $G(D)$ be the underlying simple graphs (distinct vertices adjacent when some edge joins them). Assume $N$ and $D$ are *dual* ($G(N)$ and $G(D)$ connected, $\ker\partial_N=\operatorname{im}\nabla_D$, $\ker\partial_D=\operatorname{im}\nabla_N$) and both are *simple* (no loops, no two edges with the same unordered endpoint pair).
--
--   A triangle of $D$ with edge set $s$ consists of distinct corners $u_0,u_1,u_2\in F$ and distinct edges $f_0,f_1,f_2$ with $\{f_0,f_1,f_2\}=s$ such that $f_i$ joins $u_i$ and $u_{i+1}$ (indices mod $3$). Let $\sigma_D(e,c)=1$ if $t_D(e)=c$ and $\sigma_D(e,c)=-1$ otherwise. For $v\in V$ let $\operatorname{st}_N(v)$ be the set of edges with tail or head $v$, and $\mathbf 1_v$ the indicator function of $v$.
--
--   If $v\in V$ and $\operatorname{st}_N(v)$ is the edge set of some triangle of $D$, then there is a triangle $(u_0,u_1,u_2;f_0,f_1,f_2)$ of $D$ with edge set $\operatorname{st}_N(v)$ such that
--
--   $$
--   (\nabla_N\mathbf 1_v)(f_i)=\sigma_D(f_i,u_i)\qquad\text{for } i=0,1,2.
--   $$
--
--   Since $(\nabla_N\mathbf 1_v)(f_i)$ is $+1$ if $f_i$ points into $v$ in $N$ and $-1$ if it points away from $v$, the condition says: walking around the triangle $u_0\to u_1\to u_2\to u_0$, the edge $f_i$ is traversed along its $D$-orientation exactly when it enters $v$ in $N$. Choosing such a labelling for every vertex gives all dual triangles a coherent orientation, which converts flows of $N$ into signed sums over corners of the dual triangles.
--
--   **Formalization Note** The triangle structure is `D.Triangle (N.star v)` with fields `corner` and `edge`; the theorem takes one such structure `t` as input and returns `u` of the same type. $\sigma_D$ is `D.arcSign`. Neither $V$ nor $F$ needs to be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Circulation.lean#L98-L144

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

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
theorem OAI.Barnette.Network.oriented_face (h : N.Duality D) (sN : N.Simple) (sD : D.Simple)
    (v : V) (t : D.Triangle (N.star v)) :
    ∃ u : D.Triangle (N.star v), ∀ i,
      N.gradient (fun w => if w = v then 1 else 0) (u.edge i) =
        D.arcSign (u.edge i) (u.corner i) := by sorry
