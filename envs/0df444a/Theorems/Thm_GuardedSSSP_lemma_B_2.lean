-- Prove2me | Theorems.Thm_GuardedSSSP_lemma_B_2
-- name    : GuardedSSSP.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:20.271715+00:00
-- url     : https://prove2.me/theorems/d3829ea9-3f5e-47f5-8616-a325f5b614dd
-- title:
--   Lemma B.2 — forward-DAG charge: $C_A(w)\ge m_F-n+1$ and $P_A(w)\ge q_F-d_s$ on one execution
-- statement:
--   Let $\prec$ be a rooted order of a directed multigraph $G$ with $n$ vertices and source $s$: $s$ is first and every other vertex has an incoming arc from an earlier vertex. Let $F$ be the set of forward arcs (tail before head), $m_F=|F|$, $q_F$ the number of distinct (tail, head) pairs of arcs in $F$, and $d_s$ the number of those pairs with tail $s$. Then for every correct topology-specialized comparison–addition program $A$ for $(G,s)$ there is one weighting $w$ with $w_e>0$ for every arc $e$ such that, on that single execution,
--
--   $$C_A(w)\ge m_F-n+1,\qquad P_A(w)\ge q_F-d_s.$$
--
--   This holds even though $A$ may use arbitrary real literals, mixed sums, equality branches and shared registers. It is the lower-bound engine behind Proposition B.3.
--
--   Differences from the source:
--   - encoding: C_A(w) ≥ m_F − n + 1, P_A(w) ≥ q_F − d_s → m_F + 1 ≤ C_A(w) + n and q_F ≤ P_A(w) + d_s; reason: the same inequalities without truncated subtraction in ℕ
--   - encoding: a rooted order of a reachable directed multigraph → a bijective position map with s first and an earlier in-neighbour for every v ≠ s; no separate reachability hypothesis; reason: a rooted order already makes every vertex reachable
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Lemma B.2, p.32 (PDF p.33)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_GuardedSSSP_dist
import Definitions.Def_GuardedSSSP_KCA
import Definitions.Def_GuardedSSSP_Dominates

namespace GuardedSSSP

open AtomicDynRouting.ResidenceTime

/-- **Lemma B.2** (Forward-DAG charge on one execution), p.32 (PDF p.33).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "Let ≺ be a rooted order of a reachable directed multigraph G:
the source is first and every other vertex has an incoming arc from an earlier vertex. Let F contain all
forward primitive arcs, with m_F primitives, q_F endpoint classes, and d_s source-out endpoint classes.
For every correct finite comparison–addition program A, there is one strictly positive weighting w on
which C_A(w) ≥ m_F − n + 1, P_A(w) ≥ q_F − d_s. The two inequalities hold on the same execution, even for
mixed sums, arbitrary real literals, equality branches, and cross-output sharing."

Here `F` is the set of forward arcs, `m_F = |F|`, `q_F` the number of distinct (tail, head) pairs of arcs
in `F`, and `d_s` the number of those pairs with tail `s`. The inequalities are written additively,
`m_F + 1 ≤ C_A(w) + n` and `q_F ≤ P_A(w) + d_s`, to avoid truncated subtraction in `ℕ`.

**Formalization Note.** The rooted order (`IsRootedOrder`) already makes every vertex reachable, so
"reachable" is not a separate hypothesis. A competitor (`CAProg`) may carry arbitrary real literals and
may compare and add any held registers. -/
theorem lemma_B_2 {n m : ℕ} (G : Network (Fin n) (Fin m)) (s : Fin n) (pos : Fin n ≃ Fin n)
    (hpos : IsRootedOrder G s pos) (A : CAProg n) (hA : Correct G s A) :
    let F := Finset.univ.filter (fun e : Fin m => IsForward G pos e)
    let mF := F.card
    let qF := (F.image fun e => (G.tail e, G.head e)).card
    let ds := ((F.filter fun e => G.tail e = s).image fun e => (G.tail e, G.head e)).card
    ∃ w : Fin m → ℝ, (∀ e, 0 < w e) ∧ mF + 1 ≤ A.C w + n ∧ qF ≤ A.P w + ds := by sorry

end GuardedSSSP
