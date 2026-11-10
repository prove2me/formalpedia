-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_level_work
-- name    : NearlyOptimalPPR.Computation.recursive_level_work
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:38:59.360246+00:00
-- url     : https://prove2.me/theorems/632cfaef-9c4b-4d11-a2b3-521f1c6b63a8
-- title:
--   Lemma 4.4 — Work at one recursive level
-- statement:
--   Fix the exact-SDDM model. There are absolute $C>0$ and a positive integer $c$, uniform over all graph inputs, real parameters, depths and levels. For every $0<\varepsilon\le1$, depth $\ell$ and finite block schedule, put $P=C(2+\log(2/\varepsilon)+\ell)^c$. Run Normalize from its prescribed root state on any nonisolated seed with $0<\alpha\le1/2$.
--
--   Every finite execution prefix and every created call of scale $N$ and block $b$ have at most $PN/b$ episodes and full solves. Every completed episode, and the current episode while open, has at most one child call. Every created call eventually closes, including by ancestor interruption or component completion.
--
--   Writing $R_j(N)$ for the actual uniform work envelope at level $j$, for $j<\ell$ and $N\ge1$,
--
--   $$R_j(N)\le P\left(\frac{N^2}{b}+\frac N b R_{j+1}(b)\right)+PN.$$
--
--   At the leaf, for every $N\ge1$,
--
--   $$R_\ell(N)\le P\left(\frac{N^2}{b}+Nb\right).$$
--
--   Here $b$ is the schedule's legal fixed or balanced block at that level and scale. The same $P$ is used at every level. Child initialization is charged to the parent, and a push is charged to its producing call including all open-record updates and the crossing update.
--
--   These bounds retain the full recurrence and finite-prefix counts used to establish termination and the recursive exponent improvement. Work and suprema live in nonnegative extended reals, so finiteness is asserted by the inequalities.
--
--   Differences from the source:
--   - encoding: P=C(2+log(2/epsilon)+ell)^c with sufficiently large absolute C,c → uniform existential C>0 and positive integer c before epsilon, depth, schedule, graph and level; reason: an integer exponent represents a sufficiently large polynomial overhead without input-dependent constants
--   - encoding: O(P N) in the recurrence → P N after uniform enlargement of P; reason: the source explicitly permits this enlargement on p.18
--   - encoding: counts on every finite valid execution prefix and eventual call termination → counts on operationally reachable prefixes, and eventual closure of every created call; reason: no termination or proof invariant is assumed when forming the prefix
--   - encoding: expected per-call work → the supremum of actual nonnegative charged work with deterministic idealized primitive charges; reason: the charge equals its expected value and nontermination remains infinite
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Lemma 4.4 p.18; proof §§5.3–5.4 pp.28–29

import Mathlib
import Definitions.Def_NearlyOptimalPPR_Computation_push

set_option autoImplicit false

open Finset Matrix MeasureTheory
open scoped ENNReal

namespace NearlyOptimalPPR.Computation

/-- Li, Xu, Yang, Zhou, STOC 2027 submission #884 (October 2026),
Lemma 4.4 p.18, finite-prefix and termination arguments pp.28--29.
P is uniform across inputs and levels. Its uniform enlargement absorbs the
absolute constant of O(P*N), as allowed on p.18. -/
theorem recursive_level_work (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule), 0 < ε → ε ≤ 1 →
        let P := overhead C c ε ℓ
        (∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α : ℝ),
          0 < α → α ≤ 1 / 2 → 0 < g.graph.degree s →
          ∀ (t id : ℕ) (info : CallInformation),
            let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
            (run t).information id = some info →
              ((run t).episodes id : ℝ) ≤ P * info.scale / info.block ∧
              ((run t).fullSolves id : ℝ) ≤ P * info.scale / info.block ∧
              (∀ k ∈ (run t).episodeChildCounts id, k ≤ 1) ∧
              (∀ i ≤ (run t).top, ((run t).frames i).id = id →
                ((run t).frames i).childrenThisEpisode ≤ 1) ∧
              ∃ t' ≥ t, id ∈ (run t').closed) ∧
        (∀ (j : ℕ) (N : ℝ), j < ℓ → 1 ≤ N →
          let b := blockScale schedule ℓ j N
          workEnvelope m ε ℓ schedule j N ≤
            ENNReal.ofReal P *
              (ENNReal.ofReal (N ^ 2 / b) +
                ENNReal.ofReal (N / b) * workEnvelope m ε ℓ schedule (j + 1) b) +
              ENNReal.ofReal (P * N)) ∧
        (∀ N : ℝ, 1 ≤ N →
          let b := blockScale schedule ℓ ℓ N
          workEnvelope m ε ℓ schedule ℓ N ≤ ENNReal.ofReal (P * (N ^ 2 / b + N * b))) := by sorry

end NearlyOptimalPPR.Computation
