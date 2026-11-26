-- Prove2me | Theorems.Thm_GuardedSubstitution_Readout_exact_morphic_readout
-- name    : GuardedSubstitution.Readout.exact_morphic_readout
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T19:31:32.938814+00:00
-- url     : https://prove2.me/theorems/a6bfa2b5-8bb9-490f-a240-b74e97558caa
-- title:
--   Exact state readout for substitution-generated guarded affine runs
-- statement:
--   Fix a deterministic transition on a vector space over a field. Each symbol specifies an affine update and a scalar equality guard, and the transition agrees with that update on states satisfying that guard. A finite substitution rule, starting symbol, and depth specify a finite word of scheduled updates. Cache each block's homogeneous linear update and the subspace admitted by its guards. If the expansion covers a horizon $T$ and the lifted initial state belongs to the admissible subspace of its length-$T$ prefix, then for every time $t$ up to $T$ the cached update for the length-$t$ prefix gives exactly the true state at time $t$, with homogeneous coordinate one.
-- source:
--   Uses the whole-block and partial-child decomposition from grammar-compressed access. See Bille et al., Random Access to Grammar-Compressed Strings and Trees, Section 3, https://arxiv.org/abs/1001.1565. The guarded readout theorem is proved here.

import Definitions.Def_GuardedSubstitutionReadout

open GuardedSubstitution.Prefixes GuardedSubstitution.Chunks GuardedSubstitution.Readout
open GuardedSubstitution.Affine (affineStep)

theorem GuardedSubstitution.Readout.exact_morphic_readout {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] {k : ℕ} [DecidableEq K] (rule : Fin k → List (Fin k))
    (action : Fin k → Action K V) (depth : ℕ) (label : Fin k)
    (T : ℕ) (start : V) (step : V → V)
    (onBranch : ∀ (a : Fin k) (x : V), (action a).probe x + (action a).bias = (action a).expected →
      step x = affineStep (action a).linear (action a).translate x)
    (fits : T ≤ ((build rule (Action.summary ∘ action) depth).top.get label).length)
    (allowed : (start, (1 : K)) ∈ (prefixSummary rule action depth label T).admissible) :
    ∀ t ≤ T, (prefixSummary rule action depth label t).update (start,1) =
      (step^[t] start,1) := by sorry
