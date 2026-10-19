-- Prove2me | Theorems.Thm_OAI_Barnette_Network_range_internal_boundary
-- name    : OAI.Barnette.Network.range_internal_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:10:34.449751+00:00
-- url     : https://prove2.me/theorems/886bff30-d335-4893-8a62-181ccaa74728
-- title:
--   Boundaries of flows on internal edges are exactly the vertex functions with zero sum on every fibre
-- statement:
--   Let $V,W,E$ be finite sets, let $N$ be a network with vertex set $V$ and edge set $E$ (a pair of maps $\mathrm{tail},\mathrm{head}:E\to V$), and let $q:V\to W$. An edge is *internal* if both endpoints lie in the same fibre of $q$; write
--
--   $$E_q=\{e\in E:\ q(\mathrm{tail}\,e)=q(\mathrm{head}\,e)\}$$
--
--   and let $N_q$ be the network with vertex set $V$, edge set $E_q$ and the same tail and head maps. Its underlying graph joins distinct $v,w$ iff some internal edge has endpoint pair $\{v,w\}$. The map $q$ has *connected fibres* (with respect to $N$) if any two vertices $v,w$ with $q(v)=q(w)$ are joined by a walk in this graph. The boundary of $x:E_q\to\mathbb{R}$ is $(\partial_{N_q}x)(v)=\sum_{e\in E_q:\,\mathrm{head}(e)=v}x_e-\sum_{e\in E_q:\,\mathrm{tail}(e)=v}x_e$, and the push-forward $q_*:\mathbb{R}^V\to\mathbb{R}^W$ is $(q_*y)(w)=\sum_{v:\,q(v)=w}y(v)$.
--
--   **Theorem.** If $q$ is surjective and has connected fibres, then
--
--   $$\operatorname{im}\partial_{N_q}=\ker q_* .$$
--
--   Equivalently, a function $y:V\to\mathbb{R}$ is the boundary of some flow on internal edges if and only if $\sum_{v\in q^{-1}(w)}y(v)=0$ for every $w\in W$. Flows inside connected clusters of vertices can thus realise exactly those vertex demands that balance within each cluster. This is the linear-algebra input for contracting every fibre of $q$ to a single vertex and comparing the flow spaces of a network with those of the contracted network.
--
--   **Formalization Note** $N_q$ is `N.restrict (Subtype.val : N.internal q → E)`, $q_*$ is `push q`, and connected fibres is `N.ConnectedFibers q`. The equality is between submodules of `V → ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Quotients.lean#L169-L190

import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients

open OAI OAI.Barnette OAI.Barnette.Network
variable {V W E K : Type*}
open scoped Classical
variable [Fintype V] [Fintype W] [Fintype E] [Fintype K]

theorem OAI.Barnette.Network.range_internal_boundary (N : Network V E) {q : V → W}
    (hq : Function.Surjective q) (hc : N.ConnectedFibers q) :
    (N.restrict (Subtype.val : N.internal q → E)).boundary.range = (push q).ker := by sorry
