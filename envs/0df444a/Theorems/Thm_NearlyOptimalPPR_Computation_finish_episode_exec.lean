-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_finish_episode_exec
-- name    : NearlyOptimalPPR.Computation.finish_episode_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:38.452281+00:00
-- url     : https://prove2.me/theorems/46b8407b-82b4-4d71-bb5f-6d8456b31107
-- title:
--   Episode completion clears the cache with exact charged work
-- statement:
--   Assume a valid recursive memory representation, valid keys, top level at most $\ell$, and a stored current active set. Let $C$ be the current cache and $w=16(\ell+3)$. The episode-finish routine has a finite execution representing the source episode-completion transition, using exactly
--
--   $$t=(4w+17)|C|+60$$
--
--   instructions. Its heap mass is unchanged, and its charged work increases by exactly $t$. It preserves output and graph-query count and leaves the machine ready to continue.
--
--   This contract isolates the cache-clearing cost that is paid by the cache component of the controller potential.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Algorithms 1 and 6–9, pp. 5,14–22; charged local-machine realization of the mission computational model.

import Definitions.Def_NearlyOptimalPPR_Computation_compiler_runtime
open Finset Matrix
open scoped ENNReal
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace NearlyOptimalPPR.Computation
open SparseQueue
theorem finish_episode_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored) (hKeys : KeysInvariant g logical) :
    ∃ out, ∃ memory : RecursiveMachineMemory g s α ε ell length (finishEpisode logical) out,
      MachineEval m g ω finishEpisodeCode st
        ((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+60) out ∧
      memory.queueMass=pm.queueMass ∧
      out.work=st.work+((4*(16*(ell+3))+17)*(logical.frames logical.top).cache.card+60 : ℕ) ∧
      out.scalar.queries=st.scalar.queries ∧ out.output=st.output ∧ out.scalar.halted=false := by sorry
end NearlyOptimalPPR.Computation
