-- Prove2me | Theorems.Thm_IntervalExplore_KT1_theorem_2
-- name    : IntervalExplore.KT1.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:04.488468+00:00
-- url     : https://prove2.me/theorems/7b0c00bb-2d2b-4b7b-a2f3-9719adf945f0
-- title:
--   Theorem 2 — uniform deterministic KT1 exploration and termination
-- statement:
--   There exist a natural-number constant $c\ge1$ and one deterministic observation-only algorithm $A$ with the following property. Let $G=(V,E)$ be any finite simple undirected graph with $n=|V|\ge3$ and $m=|E|\ge n$, with arbitrary distinct identifiers, fixed port numberings and starting vertex. For every schedule of subgraphs of $G$ that is $\tau_c(n,m)$-interval-connected, the single agent running $A$ visits every vertex and terminates within $\tau_c(n,m)$ time, where
--   $$
--   \xi(n,m)=\frac{\ln n}{1+\ln m-\ln n},\qquad
--   \tau_c(n,m)=c\left\lceil\xi(n,m)m+n(\ln n)^2\right\rceil.
--   $$
--   The paper writes $O(\xi(n,m)m+n\log^2 n)$; the proof uses precisely this witness with a sufficiently large universal $c$ (§2, p.5). The same quantity is the connectivity window and the deadline. Both $c$ and $A$ are fixed before the instance, and $A$ sees only local observation history, not $n$, $m$, the schedule or the window size. Simplicity gives the printed upper endpoint $m\le\binom n2$ automatically. This is the mission's full-strength goal.
--
--   Differences from the source:
--   - encoding: τ(n,m)=O(ξ(n,m)m+n log² n) → the §2 witness τ=c*ceil(ξ(n,m)m+n(ln n)²), with ∃c≥1 before every instance; reason: this is the function used by the paper’s proof and has the printed asymptotic order
--   - encoding: one deterministic KT1 algorithm in an unknown graph → one function from finite fixed-universe observations to a port or termination, with invalid ports permanently stuck; reason: the function is chosen before all world data, receives exactly the KT1 interface and must both visit every vertex and terminate
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Theorem 2, p.4 (PDF p.5), with the §2 witness, p.5 (PDF p.6)

import Definitions.Def_IntervalExplore_KT1_Execution
import Definitions.Def_IntervalExplore_KT1_Rates

set_option autoImplicit false

namespace IntervalExplore.KT1

/-- Theorem 2, p.4 (PDF p.5), with the exact §2, p.5 (PDF p.6) window witness.
One deterministic observation-only algorithm and one absolute c work for all instances.
The same tau controls the connectivity window and the deadline for visiting AND terminating. -/
theorem theorem_2 :
    ∃ c : ℕ, 1 ≤ c ∧ ∃ A : Alg,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (W : World V),
        3 ≤ Fintype.card V → Fintype.card V ≤ edgeCount W.graph →
        IntervalConnected W.dynamic (tau c (Fintype.card V) (edgeCount W.graph)) →
        ExploresWithin W A (tau c (Fintype.card V) (edgeCount W.graph)) := by sorry

end IntervalExplore.KT1
