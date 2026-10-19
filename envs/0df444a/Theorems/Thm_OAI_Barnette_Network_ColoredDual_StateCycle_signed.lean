-- Prove2me | Theorems.Thm_OAI_Barnette_Network_ColoredDual_StateCycle_signed
-- name    : OAI.Barnette.Network.ColoredDual.StateCycle.signed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:26:37.805602+00:00
-- url     : https://prove2.me/theorems/39f55ccf-e5fb-413e-a546-4454665b9ee2
-- title:
--   Sign rule for state cycles: index sum $\pm 3$ with slope of the opposite sign
-- statement:
--   **Setting.** Let $N$ (vertex set $V$) and $D$ (vertex set $F$) be oriented networks on a common edge set $E$, all three sets finite, with tail and head maps $t_N,h_N:E\to V$ and $t_D,h_D:E\to F$. Write $(\nabla_N g)(e)=g(h_N(e))-g(t_N(e))$ for $g:V\to\mathbb{R}$ and $(\partial_N x)(u)=\sum_{e:\,h_N(e)=u}x(e)-\sum_{e:\,t_N(e)=u}x(e)$ for $x:E\to\mathbb{R}$, and define $\nabla_D,\partial_D$ in the same way. Let $\sigma_D(e,z)=1$ if $t_D(e)=z$ and $\sigma_D(e,z)=-1$ otherwise, $\operatorname{st}(u)=\{e: t_N(e)=u\text{ or }h_N(e)=u\}$, $\mathbf 1_S$ the indicator of a set $S$, and let $G_N,G_D$ be the underlying simple graphs (distinct vertices are adjacent when some edge joins them). A colored dual structure on $(N,D)$ consists of:
--
--   1. duality: $G_N$ and $G_D$ are connected, $\ker\partial_N=\operatorname{im}\nabla_D$ and $\ker\partial_D=\operatorname{im}\nabla_N$;
--   2. simplicity: $N$ and $D$ have no loops and no two edges with the same unordered pair of endpoints; moreover $G_N$ is $3$-regular;
--   3. a set $B\subseteq V$ of black vertices such that every edge has exactly one black endpoint;
--   4. for every $u\in V$ an oriented face triangle on $\operatorname{st}(u)$: distinct corners $c^u_0,c^u_1,c^u_2\in F$ and distinct edges $e^u_0,e^u_1,e^u_2$ with $\{e^u_0,e^u_1,e^u_2\}=\operatorname{st}(u)$, where $e^u_k$ joins $c^u_k$ and $c^u_{k+1}$ in $D$ ($k\in\mathbb{Z}/3$), and $(\nabla_N\mathbf 1_{\{u\}})(e^u_k)=\sigma_D(e^u_k,c^u_k)$.
--
--   **States and state cycles.** Fix a root $\rho\in V$, put $B^\circ=B\setminus\{\rho\}$ and $X=F\setminus\{c^\rho_0,c^\rho_1,c^\rho_2\}$. A state is a map $s:B^\circ\to\mathbb{Z}/3$ such that $b\mapsto c^b_{s(b)}$ is a bijection from $B^\circ$ onto $X$. A state cycle $C$ for $s$ consists of a cycle $z_0,\dots,z_{m-1}$ of $G_D$ (with $m\ge 3$, distinct vertices, $z_i$ adjacent to $z_{i+1}$, indices modulo $m$) together with $b_i\in B^\circ$ and $k_i\in\mathbb{Z}/3$ such that $c^{b_i}_{s(b_i)}=z_i$ and $c^{b_i}_{k_i}=z_{i+1}$ for all $i$. With $\delta(k,k)=0$, $\delta(k,k+1)=1$, $\delta(k,k-1)=-1$ on $\mathbb{Z}/3$, the index sum of $C$ is $\Delta(C)=\sum_{i}\delta(s(b_i),k_i)$.
--
--   **Slope and white charge.** For $\alpha:E\to\mathbb{R}$ and $u\in V$ let $p^u_\alpha:\mathbb{Z}/3\to\mathbb{R}$ be the face potential $p^u_\alpha(0)=0$, $p^u_\alpha(1)=\alpha(e^u_0)\,\sigma_D(e^u_0,c^u_0)$, $p^u_\alpha(2)=p^u_\alpha(1)+\alpha(e^u_1)\,\sigma_D(e^u_1,c^u_1)$, and define the slope $S_\alpha(C)=\sum_i\big(p^{b_i}_\alpha(k_i)-p^{b_i}_\alpha(s(b_i))\big)$. The white charge is $w(u)=[u\notin B]-[u=\rho]\cdot|V\setminus B|$, where $[\cdot]$ is the Iverson bracket.
--
--   **Theorem.** If $\partial_N\alpha=w$, then
--
--   $$\big(\Delta(C)=-3\ \text{ and }\ S_\alpha(C)>0\big)\quad\text{or}\quad\big(\Delta(C)=3\ \text{ and }\ S_\alpha(C)<0\big).$$
--
--   Thus every cycle traced by a state through face triangles of black vertices has index sum exactly $\pm3$, and a flow $\alpha$ that delivers one unit to every white vertex out of the root detects its direction: the slope has the sign opposite to the index sum. This is the sign hypothesis needed by the forest-extraction argument for paired incidence states in the Hamiltonicity proof for cubic bipartite planar three-connected graphs.
--
--   **Formalization Note** The structure is `M : N.ColoredDual D`, states are `M.State root` (states of the triangle system `M.system root` on `M.nonroots root`), and `C : M.StateCycle s` has fields `cycle`, `face` (the $b_i$, not required to be injective) and `corner` (the $k_i$). $\Delta(C)$ is the integer `C.delta`, $S_\alpha(C)$ is `C.slope α` with $p^u_\alpha$ given by `M.weights α root`, and $w$ is `whiteCharge M.black root`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/ColoredDual.lean#L183-L203

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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual

open OAI OAI.Barnette OAI.Barnette.Network OAI.Barnette.Network.ColoredDual OAI.Barnette.Network.ColoredDual.StateCycle
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D)
variable {M} {root : V} {s : M.State root} (C : M.StateCycle s)

theorem OAI.Barnette.Network.ColoredDual.StateCycle.signed (α : E → ℝ) (hα : N.boundary α = whiteCharge M.black root) :
    (C.delta = -3 ∧ 0 < C.slope α) ∨ (C.delta = 3 ∧ C.slope α < 0) := by sorry
