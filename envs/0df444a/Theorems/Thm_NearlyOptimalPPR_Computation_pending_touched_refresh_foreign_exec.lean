-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_pending_touched_refresh_foreign_exec
-- name    : NearlyOptimalPPR.Computation.pending_touched_refresh_foreign_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:45:50.2603+00:00
-- url     : https://prove2.me/theorems/0413dad3-bf81-46ce-8332-7178c17f5e34
-- title:
--   Touched-vertex refresh restores complete recursive queue representations
-- statement:
--   Let a pending recursive memory record represent a logical state whose numeric and domain data are valid, with any missing queue coverage confined to a stored source vertex and its neighbors. Assume exterior/high queue coverage and high Boolean records already hold outside that touched set. Let $d$ be the source degree, $h$ the top level, $w=16(\ell+3)$ the record width, and $r$ a queue rank covering the stated capacity. The touched-refresh routine has a finite execution returning a complete recursive memory representation, with
--
--   $$t\le(d+1)((h+1)(42r+60w+284)+4w+25)+10,$$
--
--   and heap mass increasing by at most $2(h+1)(d+1)$. It restores the exterior and high predicates at every relevant level, preserves output and graph-query count, and preserves all nonnegative real-memory cells and the specified foreign integer-buffer frame. Charged work increases by exactly $t$.
--
--   The contract permits temporary missing coverage after a numeric update and restores it without scanning the graph.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Algorithms 1 and 6–9, pp. 5,14–22; charged local-machine realization of the mission computational model.

import Definitions.Def_NearlyOptimalPPR_Computation_compiler_runtime
import Definitions.Def_NearlyOptimalPPR_Computation_compiler_buffers
open Finset Matrix
open scoped ENNReal
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace NearlyOptimalPPR.Computation
open SparseQueue
theorem pending_touched_refresh_foreign_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε : ℝ) (ell length N R : ℕ) (logical : RecursiveState n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : MachinePendingKeys g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hActiveDomain : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hExtDomain : ∀ i ≤ logical.top, (logical.frames i).exterior ⊆ parentDomain logical i)
    (hHighDomain : ∀ i ≤ logical.top, (logical.frames i).high ⊆ parentDomain logical i)
    (source : Fin n) (hs : source ∈ logical.stored)
    (hSource : st.scalar.core.ptrs 116=(source.val : ℤ)) (hVertex : st.scalar.core.ptrs 40=(source.val : ℤ))
    (hDegree : st.scalar.core.ptrs 120=((g.neighbors source).length : ℤ))
    (hMass : pm.queueMass+2*(logical.top+1)*((g.neighbors source).length+1) ≤ N) (hCap : R < length) (hPow : N < 2^R)
    (hExtOutside : ∀ i, ∀ hi : i ≤ logical.top,
      (logical.frames i).exterior.image Fin.val \ (insert source (g.neighbors source).toFinset).image Fin.val ⊆ (pm.frames i hi).exteriorObject.keys)
    (hHighOutside : ∀ i, ∀ hi : i ≤ logical.top,
      (logical.frames i).high.image Fin.val \ (insert source (g.neighbors source).toFinset).image Fin.val ⊆ (pm.frames i hi).highObject.keys)
    (hBoolOutside : ∀ i ≤ logical.top,
      HighBooleanRecords st.scalar.integerMemory st.scalar.core.mem (16*(ell+3)) (16*(i+1)) (logical.frames i).theta
        (parentDomain logical i \ insert source (g.neighbors source).toFinset)) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω pendingTouchedRefreshCode st steps out ∧
      steps ≤ ((g.neighbors source).length+1)*((logical.top+1)*(42*R+60*(16*(ell+3))+284)+4*(16*(ell+3))+25)+10 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*((g.neighbors source).length+1) ∧
      out.scalar.core.ptrs 40=(source.val : ℤ) ∧ out.scalar.queries=st.scalar.queries ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ z : ℤ, 0 ≤ z → out.scalar.core.mem z=st.scalar.core.mem z) ∧ PendingIntegerFrame pm (MachinePendingKeys.ofMemory memory) := by sorry
end NearlyOptimalPPR.Computation
