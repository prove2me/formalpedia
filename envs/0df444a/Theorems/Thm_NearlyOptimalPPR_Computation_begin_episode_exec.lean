-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_begin_episode_exec
-- name    : NearlyOptimalPPR.Computation.begin_episode_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:47.490918+00:00
-- url     : https://prove2.me/theorems/761b8891-6ad7-4bd9-a3db-a24466821f35
-- title:
--   Episode initialization executes the source transition with bounded work
-- statement:
--   Suppose the recursive memory representation, region invariant, stored active-set condition, and queue-capacity conditions hold. Let $A$ be the current active set and $h$ the top level. The episode-begin routine has a finite execution representing exactly the source episode-initialization transition, with
--
--   $$M'\le M+2(h+1)|A|.$$
--
--   Its instruction count is bounded by the explicit record-width, queue-rank, and level-dependent coefficient times $|A|$, plus the fixed header allowance. Charged work increases by that count. The routine preserves graph-query count, output, and all solve-epoch marks and remains ready for further execution.
--
--   The contract includes active-reference initialization, residual and budget preparation, cache clearing, and queue refresh.
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
theorem begin_episode_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hDepth : logical.top ≤ ell) (hRegion : RegionInvariant logical)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hMass : pm.queueMass+2*(logical.top+1)*(logical.frames logical.top).active.card ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (compilerBeginEpisode m g logical) out,
      MachineEval m g ω beginEpisodeCode st steps out ∧
      steps ≤ ((2*(4*(16*(ell+3))+17)+10)+
        ((logical.top+1)*(42*rank+60*(16*(ell+3))+284)+11))*
        (logical.frames logical.top).active.card+188 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*(logical.frames logical.top).active.card ∧
      out.work=st.work+steps ∧ out.scalar.queries=st.scalar.queries ∧
      out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ z : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) z.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) z.val 7)) := by sorry
end NearlyOptimalPPR.Computation
