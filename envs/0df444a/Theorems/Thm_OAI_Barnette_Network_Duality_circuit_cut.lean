-- Prove2me | Theorems.Thm_OAI_Barnette_Network_Duality_circuit_cut
-- name    : OAI.Barnette.Network.Duality.circuit_cut
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:06:19.560876+00:00
-- url     : https://prove2.me/theorems/31254d90-e35b-40f9-8bfc-d32bd4057e07
-- title:
--   Flow circuits of a dual network are nonzero multiples of gradients of cut indicators
-- statement:
--   A *network* with vertex set $X$ and edge set $E$ is a pair of maps $\mathrm{tail},\mathrm{head}:E\to X$; its underlying graph $G(\cdot)$ is the simple graph on $X$ in which distinct $p,p'$ are adjacent iff some edge has endpoint pair $\{p,p'\}$. For such a network $N$ with $E$ finite, the gradient $\nabla_N:\mathbb{R}^X\to\mathbb{R}^E$ and the boundary $\partial_N:\mathbb{R}^E\to\mathbb{R}^X$ are the linear maps
--
--   $$(\nabla_N f)(e)=f(\mathrm{head}\,e)-f(\mathrm{tail}\,e),\qquad(\partial_N x)(p)=\sum_{e:\ \mathrm{head}(e)=p}x_e-\sum_{e:\ \mathrm{tail}(e)=p}x_e .$$
--
--   An edge function $x$ is a *circulation* of $N$ if $\partial_N x=0$, and $\operatorname{supp}x=\{e:\ x_e\ne0\}$ is its support. A *flow circuit* of $N$ is a circulation $x\ne0$ of minimal support in the following sense: every circulation $y$ of $N$ with $\operatorname{supp}y\subseteq\operatorname{supp}x$ satisfies $y=0$ or $\operatorname{supp}y=\operatorname{supp}x$.
--
--   Now let $N$ be a network with vertex set $V$ and $D$ a network with vertex set $F$, both with the same finite edge set $E$. They are *in duality* if $G(N)$ and $G(D)$ are connected and
--
--   $$\ker\partial_N=\operatorname{im}\nabla_D,\qquad \ker\partial_D=\operatorname{im}\nabla_N .$$
--
--   For a finite set $A\subseteq V$, $\mathbf 1_A$ is its indicator function and the *cut* $\delta_N(A)$ is the set of edges of $N$ with exactly one endpoint in $A$.
--
--   **Theorem.** Let $V$ be finite, let $N$ (on $V$) and $D$ (on $F$) be in duality, let $x$ be a flow circuit of $D$, and let $r\in V$ be any vertex. Then there exist a nonempty set $A\subseteq V$ with $r\notin A$ and a real number $c\ne0$ such that
--
--   $$x=c\,\nabla_N\mathbf 1_A\qquad\text{and}\qquad\delta_N(A)=\operatorname{supp}x .$$
--
--   Thus every minimal circulation of the dual network is a nonzero multiple of the signed indicator vector of a cut of the primal network, and the shore $A$ can be chosen to avoid any prescribed vertex. This is one half of the correspondence between circuits of $D$ and bonds (minimal cuts) of $N$; the companion result shows that a cut arising in this way is a bond.
--
--   **Formalization Note** The hypotheses are `N.Duality D` and `D.FlowCircuit x`; $A$ is a `Finset V`, $\mathbf 1_A$ is `fun v => if v ∈ A then 1 else 0`, $\delta_N(A)$ is `N.cut A` and $\operatorname{supp}x$ is `D.flowSupport x`. Finiteness of the face set $F$ is not assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/FlowCircuits.lean#L69-L123

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
theorem OAI.Barnette.Network.Duality.circuit_cut (h : N.Duality D) (x : E → ℝ)
    (hx : D.FlowCircuit x) (root : V) :
    ∃ (A : Finset V) (c : ℝ), A.Nonempty ∧ root ∉ A ∧ c ≠ 0 ∧
      x = c • N.gradient (fun v => if v ∈ A then 1 else 0) ∧
      N.cut A = D.flowSupport x := by sorry
