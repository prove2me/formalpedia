-- Prove2me | Theorems.Thm_OAI_Barnette_TriangleSystem_Pair_forest_pair_of_disk_circulation
-- name    : OAI.Barnette.TriangleSystem.Pair.forest_pair_of_disk_circulation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:31:00.441981+00:00
-- url     : https://prove2.me/theorems/fad5e05d-b705-41c7-8d30-ed2596fef258
-- title:
--   Sign-coherent cycles force a partner pair whose second state has a forest opposite graph
-- statement:
--   **Setting.** Let $(\tau_t)_{t\in A}$ be a triangle system on a vertex set $V$ with finite index set $A$ (each $\tau_t:\mathbb{Z}/3\to V$ injective; two triangles sharing two corners coincide), and fix $X\subseteq V$. A state on $X$ is a map $s:A\to\mathbb{Z}/3$ such that $t\mapsto\tau_t(s(t))$ is a bijection from $A$ onto $X$. A pair is an ordered pair $P=(r,s)$ of states on $X$ that are partners, i.e. $\tau_t(r(t))\ne\tau_t(s(t))$ for every $t$; $r$ is its first and $s$ its second state. The opposite graph $G_s$ of a state $s$ joins two distinct vertices when they are the two corners of some triangle $t$ other than $\tau_t(s(t))$. Opposite cycles $C$ of $s$, and the cyclic index sum $\Delta_C(r)$ of a partner $r$ along $C$, are defined as follows: $C$ is a cycle $z_0,\dots,z_{m-1}$ of $G_s$ ($m\ge 3$) with an injective $f:\mathbb{Z}/m\to A$ such that $z_k,z_{k+1}$ are corners of $f(k)$ different from $\tau_{f(k)}(s(f(k)))$, and
--   $$\Delta_C(r)=\sum_{k\in\mathbb{Z}/m}\delta\big(r(f(k)),\theta(r(f(k)),s(f(k)))\big),$$
--   where on $\mathbb{Z}/3$ we put $\delta(a,a)=0$, $\delta(a,a+1)=1$, $\delta(a,a-1)=-1$ and $\theta(a,b)=-(a+b)$.
--
--   **Cycles of a pair.** For a pair $P=(r,s)$ let $\pi_P$ be the permutation of $A$ with $\tau_{\pi_P(t)}(r(\pi_P(t)))=\tau_t(s(t))$: it sends $t$ to the triangle at which $r$ selects the vertex that $s$ selects at $t$. For an orbit $c$ of $\pi_P$ and a weight $w:A\times\mathbb{Z}/3\to\mathbb{R}$ put
--   $$\Delta_P(c)=\sum_{t\in c}\delta(r(t),s(t)),\qquad S^w_P(c)=\sum_{t\in c}w(t,s(t))-\sum_{t\in c}w(t,r(t)).$$
--
--   **Theorem.** Assume that
--
--   1. at least one pair exists;
--   2. for every state $s$ on $X$, every opposite cycle $C$ of $s$ and every partner $r$ of $s$, $\Delta_C(r)\in\{3,-3\}$;
--   3. for some weight $w$, every pair $P$ and every orbit $c$ of $\pi_P$ satisfy $\big(\Delta_P(c)=-3$ and $S^w_P(c)>0\big)$ or $\big(\Delta_P(c)=3$ and $S^w_P(c)<0\big)$.
--
--   Then there is a pair whose second state has an acyclic opposite graph:
--
--   $$\exists\ \text{pair } (r,s):\qquad G_s\ \text{is a forest}.$$
--
--   This is the abstract core of the forest-extraction step in the Hamiltonicity proof for cubic bipartite planar three-connected graphs. For the triangle system of face triangles of black vertices in a colored dual, hypotheses 2 and 3 are both consequences of the sign rule for state cycles, and the conclusion provides an incidence state whose opposite graph is a forest.
--
--   **Formalization Note** Pairs are `@Pair A V T X`, with first and second states `P.left` and `P.right`; $\pi_P$ is `P.next`, its orbits are `CycleClass P.next`, $\Delta_P(c)$ is `P.cycleDelta c`, $S^w_P(c)$ is `P.cycleSlope w c`, $\Delta_C$ is `C.cyclicDelta`, and the opposite graph is `T.oppositeGraph`. The weight $w$ has type `A → Fin 3 → ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/PairPolynomials.lean#L423-L445

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
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials

open OAI OAI.Barnette OAI.Barnette.TriangleSystem OAI.Barnette.TriangleSystem.Pair
open scoped BigOperators Polynomial
open Polynomial
variable {A V : Type*} [Fintype A] {T : TriangleSystem A V} {X : Set V}

theorem OAI.Barnette.TriangleSystem.Pair.forest_pair_of_disk_circulation (hex : Nonempty (@Pair A V T X))
    (hdisk : ∀ (s : T.State X) (C : T.OppositeCycle s) (r : T.Partners s),
      C.cyclicDelta r.val = 3 ∨ C.cyclicDelta r.val = -3)
    (w : A → Fin 3 → ℝ)
    (hsign : ∀ (P : @Pair A V T X) c,
      (P.cycleDelta c = -3 ∧ 0 < P.cycleSlope w c) ∨
      (P.cycleDelta c = 3 ∧ P.cycleSlope w c < 0)) :
    ∃ P : @Pair A V T X, (T.oppositeGraph P.right).IsAcyclic := by sorry
