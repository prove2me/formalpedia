-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_priority_exec
-- name    : NearlyOptimalPPR.Computation.priority_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:59.096172+00:00
-- url     : https://prove2.me/theorems/67d65d69-49c0-4e51-9e19-eb6e95b66168
-- title:
--   Charged priority selection preserves recursive machine memory
-- statement:
--   The priority routine scans the open recursion levels and selects exactly the pending exterior push prescribed by the logical state. It preserves that state, the input/output representation, all epoch marks, and the graph-query count. Let $h$ be the current top level, $M,M'$ the initial and final heap masses, $w=16(\ell+3)$ the vertex-record width, $r$ the queue rank, $L$ its array length, and $P$ the queue-cleaning coefficient. If the represented heap fits a capacity below $2^r$ and $r<L$, there is a finite execution with
--
--   $$M'\le M,\qquad t+PM'\le PM+(h+1)(2P+21r+20w+120)+6.$$
--
--   Here $t$ is its instruction count and the increase in charged work. The coefficient $P$ is the explicit cleaning bound in the runtime interface. The routine remains ready for the next controller instruction. This contract makes lazy queue cleanup reusable without assuming that a priority queue contains no stale entries.
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
theorem priority_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length capacity rank : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hDepth : logical.top ≤ ell) (hMass : pm.queueMass ≤ capacity) (hcap : rank < length) (hpow : capacity < 2^rank) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length logical out,
      MachineEval m g ω priorityCode st steps out ∧ PendingSelectionSpec logical out ∧
      memory.queueMass ≤ pm.queueMass ∧
      steps+(cleanBodyBound (16*(ell+3)) length rank+2)*memory.queueMass ≤
        (cleanBodyBound (16*(ell+3)) length rank+2)*pm.queueMass+
        (logical.top+1)*(2*(cleanBodyBound (16*(ell+3)) length rank+2)+(21*rank+20*(16*(ell+3))+70)+50)+6 ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by sorry
end NearlyOptimalPPR.Computation
