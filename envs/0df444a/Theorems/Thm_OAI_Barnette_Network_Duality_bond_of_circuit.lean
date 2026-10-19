-- Prove2me | Theorems.Thm_OAI_Barnette_Network_Duality_bond_of_circuit
-- name    : OAI.Barnette.Network.Duality.bond_of_circuit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:08:24.531162+00:00
-- url     : https://prove2.me/theorems/2c9b3e1f-b270-44da-bb44-8118e90e5274
-- title:
--   A cut whose edge set is the support of a dual flow circuit is a bond
-- statement:
--   A *network* with vertex set $X$ and finite edge set $E$ is a pair of maps $\mathrm{tail},\mathrm{head}:E\to X$. For a network $N$ with vertex set $V$ and a finite set $A\subseteq V$, the *cut* $\delta_N(A)$ is the set of edges with exactly one endpoint in $A$. A finite set $A\subseteq V$ is a *bond* of $N$ if its cut is a minimal nonempty cut:
--
--   $$\delta_N(A)\ne\varnothing\quad\text{and}\quad\text{for every finite } B\subseteq V:\ \ \delta_N(B)\subseteq\delta_N(A)\ \Longrightarrow\ \delta_N(B)=\varnothing\ \text{ or }\ \delta_N(B)=\delta_N(A).$$
--
--   The underlying graph $G(\cdot)$ of a network joins distinct vertices $p,p'$ iff some edge has endpoint pair $\{p,p'\}$. The gradient of $f:X\to\mathbb{R}$ is $(\nabla f)(e)=f(\mathrm{head}\,e)-f(\mathrm{tail}\,e)$, the boundary of $x:E\to\mathbb{R}$ is $(\partial x)(p)=\sum_{\mathrm{head}(e)=p}x_e-\sum_{\mathrm{tail}(e)=p}x_e$, a *circulation* is an $x$ with $\partial x=0$, and $\operatorname{supp}x=\{e:\ x_e\ne0\}$. Let $N$ have vertex set $V$ and $D$ vertex set $F$, with the same edge set $E$. They are *in duality* if $G(N)$ and $G(D)$ are connected, $\ker\partial_N=\operatorname{im}\nabla_D$ and $\ker\partial_D=\operatorname{im}\nabla_N$. A *flow circuit* of $D$ is a circulation $x\ne0$ of $D$ such that every circulation $y$ of $D$ with $\operatorname{supp}y\subseteq\operatorname{supp}x$ satisfies $y=0$ or $\operatorname{supp}y=\operatorname{supp}x$.
--
--   **Theorem.** Let $N$ and $D$ be in duality, let $x$ be a flow circuit of $D$, and let $A\subseteq V$ be a finite set with
--
--   $$\delta_N(A)=\operatorname{supp}x .$$
--
--   Then $A$ is a bond of $N$.
--
--   Combined with the result that every flow circuit of $D$ is a multiple of $\nabla_N\mathbf 1_A$ for a set $A$ with $\delta_N(A)=\operatorname{supp}x$, this shows that the supports of flow circuits of $D$ are bonds of $N$: circuits on one side of the duality are minimal cuts on the other.
--
--   **Formalization Note** $A$ and $B$ range over `Finset V`; the vertex type $V$ and the face type $F$ need not be finite (for finite $V$ the condition on $B$ concerns all subsets). The conclusion is `N.Bond A`, whose fields are `nonempty` and `minimal`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Bonds.lean#L108-L124

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds

open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
theorem OAI.Barnette.Network.Duality.bond_of_circuit (h : N.Duality D) (x : E → ℝ) (hx : D.FlowCircuit x)
    (A : Finset V) (hA : N.cut A = D.flowSupport x) : N.Bond A := by sorry
