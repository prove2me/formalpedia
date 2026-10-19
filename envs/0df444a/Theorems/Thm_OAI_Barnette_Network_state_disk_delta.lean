-- Prove2me | Theorems.Thm_OAI_Barnette_Network_state_disk_delta
-- name    : OAI.Barnette.Network.state_disk_delta
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:19:37.619621+00:00
-- url     : https://prove2.me/theorems/2f79e873-1d4d-429c-b604-0b8f79e786d1
-- title:
--   Signed disk identity: a state cycle bounds a disk and has black index sum $-3c$, $c=\pm1$
-- statement:
--   **Setting.** Let $N$ and $D$ be networks on a common finite edge set $E$ with finite vertex sets $V$ and $F$; every edge $e$ has a tail and a head, $t_N(e),h_N(e)\in V$ and $t_D(e),h_D(e)\in F$. Write $\nabla_N f(e)=f(h_N(e))-f(t_N(e))$ and $\partial_N x(v)=\sum_{e:\,h_N(e)=v}x(e)-\sum_{e:\,t_N(e)=v}x(e)$, similarly for $D$, and let $G(N)$, $G(D)$ be the underlying simple graphs (distinct vertices adjacent when some edge joins them). Assume:
--
--   * $N$ and $D$ are *dual*: $G(N)$, $G(D)$ connected, $\ker\partial_N=\operatorname{im}\nabla_D$, $\ker\partial_D=\operatorname{im}\nabla_N$;
--   * both networks are *simple* (no loops, no two edges with the same endpoint pair) and $G(N)$ is $3$-regular;
--   * for every $v\in V$ a triangle $T_v$ of $D$ is given whose edge set is the star $\operatorname{st}_N(v)$ of edges at $v$ in $N$ (distinct corners $u_0,u_1,u_2$ and distinct edges $f_0,f_1,f_2$, $f_j$ joining $u_j,u_{j+1}$ mod $3$);
--   * $B\subseteq V$ is a set of black vertices such that every edge has exactly one black endpoint $b(e)$;
--   * $\rho\in V$ is a root and $m:V\to F$ is injective on $B\setminus\{\rho\}$, sends each $v\in B\setminus\{\rho\}$ to a corner of $T_v$, and a vertex $z\in F$ is not a corner of $T_\rho$ if and only if $z=m(v)$ for some $v\in B\setminus\{\rho\}$;
--   * $c_0,\dots,c_{k-1}$ ($k\ge3$) are distinct vertices forming a cycle $C$ of $G(D)$, $e_i$ is the edge of $D$ joining $c_i$ and $c_{i+1}$ (indices mod $k$), and $b(e_i)\neq\rho$, $m(b(e_i))=c_i$ for all $i$.
--
--   Let $\sigma_D(e,c)=1$ if $t_D(e)=c$ and $\sigma_D(e,c)=-1$ otherwise. The unit circulation around $C$ and the black index sum of $C$ are
--   $$
--   \gamma_C=\sum_{i}\sigma_D(e_i,c_i)\,\mathbf 1_{e_i},\qquad \Delta_B(C)=\sum_{i}(\nabla_N\mathbf 1_B)(e_i)\,\sigma_D(e_i,c_i),
--   $$
--   where $(\nabla_N\mathbf 1_B)(e)=[h_N(e)\in B]-[t_N(e)\in B]$. For $A\subseteq V$ let $\delta(A)$ be the edges with exactly one $N$-endpoint in $A$ and $\delta_B(A)=\{e\in\delta(A): b(e)\in A\}$.
--
--   **Statement.** There exist a set $A\subseteq V$ and a real number $c$ such that
--
--   1. $A\neq\emptyset$ and $\rho\notin A$;
--   2. $c=1$ or $c=-1$;
--   3. $\gamma_C=c\,\nabla_N\mathbf 1_A$;
--   4. $\delta(A)=\{e_0,\dots,e_{k-1}\}$;
--   5. $|\delta(A)|=2|\delta_B(A)|+3$;
--   6. $\Delta_B(C)=-3c$.
--
--   In short,
--   $$
--   \gamma_C=\pm\nabla_N\mathbf 1_A,\qquad |\delta(A)|=2|\delta_B(A)|+3,\qquad \Delta_B(C)=-3c\in\{-3,3\}.
--   $$
--
--   This is the signed disk identity for state cycles: every cycle of the dual that follows the corners selected by the incidence state $m$ bounds a disk $A$ avoiding the root, the cut edges whose endpoint inside $A$ is white outnumber those whose endpoint inside $A$ is black by exactly three, and the black index sum around the cycle is $\mp3$ with the sign tied to the orientation $c$ of $C$ relative to $A$. It feeds the sign argument for directed state cycles in the Hamiltonicity proof.
--
--   **Formalization Note** The cycle is `C : CycleCoordinates D.graph` ($k=n+3$), $e_i$ is `D.cycleEdge C i`, $\gamma_C$ is `D.cycleFlow C`, $\sigma_D$ is `D.arcSign`, $\Delta_B(C)$ is `N.blackDelta D black C`, $\delta_B(A)$ is `N.blackCut black A`, and $\mathbf 1_A$ is `fun v => if v ∈ A then 1 else 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/StateDisk.lean#L442-L478

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

theorem OAI.Barnette.Network.state_disk_delta (h : N.Duality D) (sN : N.Simple)
    (hdeg : N.graph.IsRegularOfDegree 3) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v)) (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (root : V)
    (m : V → F)
    (hm_inj : Set.InjOn m {v | black v ∧ v ≠ root})
    (hm_face : ∀ v, black v → v ≠ root → m v ∈ Set.range (face v).corner)
    (hm_range : ∀ z, z ∉ Set.range (face root).corner ↔
      ∃ v, black v ∧ v ≠ root ∧ m v = z)
    (C : Barnette.CycleCoordinates D.graph)
    (hchoice : ∀ i, N.blackEndpoint black (D.cycleEdge C i) ≠ root ∧
      m (N.blackEndpoint black (D.cycleEdge C i)) = C.vertex i) :
    ∃ (A : Finset V) (c : ℝ), A.Nonempty ∧ root ∉ A ∧ (c = 1 ∨ c = -1) ∧
      D.cycleFlow C = c • N.gradient (fun v => if v ∈ A then 1 else 0) ∧
      N.cut A = D.cycleEdges C ∧
      (N.cut A).card = 2 * (N.blackCut black A).card + 3 ∧
      N.blackDelta D black C = -3*c := by sorry
