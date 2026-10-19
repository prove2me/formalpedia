-- Prove2me | Theorems.Thm_OAI_Barnette_TriangleSystem_OppositeCycle_fixed_second_state_cancels
-- name    : OAI.Barnette.TriangleSystem.OppositeCycle.fixed_second_state_cancels
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:29:46.430952+00:00
-- url     : https://prove2.me/theorems/0d325969-7b52-4b20-b2a8-f268d669ad37
-- title:
--   Phase cancellation over the partners of a state with an opposite cycle
-- statement:
--   **Setting.** Let $(\tau_t)_{t\in A}$ be a triangle system on a vertex set $V$ with finite index set $A$: each $\tau_t:\mathbb{Z}/3\to V$ is injective, and two triangles sharing two corners coincide. Fix $X\subseteq V$. A state on $X$ is a map $s:A\to\mathbb{Z}/3$ such that $t\mapsto\tau_t(s(t))$ is a bijection from $A$ onto $X$. A state $r$ is a partner of the state $s$ if $\tau_t(r(t))\ne\tau_t(s(t))$, equivalently $r(t)\ne s(t)$, for every $t\in A$. The opposite graph of $s$ joins two distinct vertices when they are the two corners of some triangle $t$ other than its selected corner $\tau_t(s(t))$. An opposite cycle $C$ of $s$ is a cycle $z_0,\dots,z_{m-1}$ ($m\ge3$, indices modulo $m$) of this graph together with an injective map $f:\mathbb{Z}/m\to A$ and labels $p_k,q_k\in\mathbb{Z}/3\setminus\{s(f(k))\}$ with $\tau_{f(k)}(p_k)=z_k$ and $\tau_{f(k)}(q_k)=z_{k+1}$.
--
--   **Notation.** On $\mathbb{Z}/3$ let $\delta(a,a)=0$, $\delta(a,a+1)=1$, $\delta(a,a-1)=-1$, and let $\theta(a,b)=-(a+b)$, which for $a\ne b$ is the third element of $\mathbb{Z}/3$. For states $r,s$ put $\rho(r,s)=\sum_{t\in A}\delta(r(t),s(t))$, and along the opposite cycle $C$ put
--   $$\Delta_C(r)=\sum_{k\in\mathbb{Z}/m}\delta\big(r(f(k)),\,\theta(r(f(k)),s(f(k)))\big).$$
--   The phase of an integer $n$ is $\varphi(n)=\mathrm{i}^{\lfloor n/3\rfloor}\in\mathbb{C}$.
--
--   **Theorem.** Let $W$ be a complex vector space and $w\in W$. If $\Delta_C(r)\in\{3,-3\}$ for every partner $r$ of $s$, then
--
--   $$\sum_{r\ \text{partner of}\ s}\varphi\big(\rho(r,s)\big)\,w=0 .$$
--
--   In the signed generating polynomial over pairs of partner states, terms can be grouped by their second state. This lemma shows that the whole group of a state $s$ cancels as soon as the opposite graph of $s$ carries a cycle on which every partner has cyclic index sum $\pm3$. It is the cancellation half of the argument producing a state whose opposite graph is a forest.
--
--   **Formalization Note** Partners form the subtype `T.Partners s`, $\rho$ is `rawIndexSum`, $\Delta_C$ is `C.cyclicDelta`, $\theta$ is `thirdIndex` and $\varphi$ is `phase n = Complex.I ^ (n / 3)`, where Lean's integer division by the positive number $3$ rounds down. The space $W$ is any additive commutative group with a module structure over the complex numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/PairPhases.lean#L91-L105

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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases

open OAI OAI.Barnette OAI.Barnette.TriangleSystem OAI.Barnette.TriangleSystem.OppositeCycle
variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}
variable {s : T.State X} (C : T.OppositeCycle s)

theorem OAI.Barnette.TriangleSystem.OppositeCycle.fixed_second_state_cancels [Fintype A] {M : Type*} [AddCommGroup M] [Module ℂ M]
    (hdisk : ∀ r : T.Partners s, C.cyclicDelta r.val = 3 ∨ C.cyclicDelta r.val = -3)
    (weight : M) : (∑ r : T.Partners s, phase (rawIndexSum r.val s) • weight) = 0 := by sorry
