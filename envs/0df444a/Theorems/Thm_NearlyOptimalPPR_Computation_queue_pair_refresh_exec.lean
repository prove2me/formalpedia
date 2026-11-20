-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_queue_pair_refresh_exec
-- name    : NearlyOptimalPPR.Computation.queue_pair_refresh_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:45:59.646526+00:00
-- url     : https://prove2.me/theorems/9644498d-f5db-4a6b-9df5-e798bedc514d
-- title:
--   Owned exterior and high queues refresh one vertex with bounded allocation
-- statement:
--   Consider two disjoint owned rank queues for a single recursive level: the exterior queue and the high-residual queue. Assume their contexts, domain membership, queued flags, and current eligibility predicates are represented correctly. Let $v$ lie in that domain, let $w$ be the record width, and let rank $r$ and array length $L$ cover both heap masses through a capacity below $2^r$, with $r<L$. The pair-refresh routine has a finite execution with
--
--   $$t\le42r+56w+203,\qquad M'_{\rm ext}\le M_{\rm ext}+1,\qquad M'_{\rm high}\le M_{\rm high}+1.$$
--
--   Each queue retains its existing keys and inserts $v$ exactly when its corresponding current eligibility predicate holds. The high Boolean and queued flags are restored; the queue objects remain disjoint. At most six fresh integer cells are allocated. Other integer records outside the two owned objects are preserved, and only the designated high Boolean real cell changes. No graph query or output emission occurs, and work increases by exactly $t$.
--
--   This contract provides the shared bounded-allocation operation used by residual propagation and sparse solves.
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
theorem queue_pair_refresh_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (width levelBase length N R : ℕ)
    (hw : levelBase+6 < width) (extBase highBase floor : ℤ) (hFloor : 2 ≤ floor)
    (q theta : ℝ) (domain : Finset (Fin n)) (extValid highValid : Finset ℕ)
    (extObj : RankQueueObject st.scalar.integerMemory extBase length (st.scalar.core.ptrs 20) floor)
    (highObj : RankQueueObject st.scalar.integerMemory highBase length (st.scalar.core.ptrs 20) floor)
    (hSep : Disjoint highObj.cells extObj.cells)
    (ctx : ExteriorQueueContext st width levelBase (levelBase+3) length extBase floor q)
    (extData : ExteriorQueueMemory st.scalar.integerMemory st.scalar.core.mem width levelBase (levelBase+3) q domain extValid extObj.keys)
    (hZero : ∀ u ∈ domain, st.scalar.integerMemory (vertexRecordAddress width u.val (levelBase+5))=0)
    (hHighDomain : highObj.keys ⊆ domain.image Fin.val)
    (hHighFlags : QueuedFlags st.scalar.integerMemory width (levelBase+6) domain highObj.keys)
    (hHighValid : ∀ u ∈ domain, u.val ∈ highValid ↔
      st.scalar.integerMemory (vertexRecordAddress width u.val (levelBase+2)) ≠ 0 ∧
      3*theta*(st.scalar.integerMemory (vertexRecordAddress width u.val 0) : ℝ) ≤
        st.scalar.core.mem (vertexRecordAddress width u.val (levelBase+1)))
    (hHighBase : st.scalar.core.ptrs 128=highBase) (hLevel : st.scalar.core.ptrs 89=(levelBase : ℤ))
    (hOne : st.scalar.core.regs 31=1) (hTheta : st.scalar.core.regs 47=theta)
    (v : Fin n) (hv : v ∈ domain) (hVertex : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hExtMass : extObj.mass ≤ N) (hHighMass : highObj.mass ≤ N) (hCap : R < length) (hPow : N < 2^R) :
    ∃ steps out,
    ∃ newExt : RankQueueObject out.scalar.integerMemory extBase length (out.scalar.core.ptrs 20) floor,
    ∃ newHigh : RankQueueObject out.scalar.integerMemory highBase length (out.scalar.core.ptrs 20) floor,
      MachineEval m g ω queuePairRefreshCode st steps out ∧ steps ≤ 42*R+56*width+203 ∧
      newExt.keys=(if v.val ∈ extValid then insert v.val extObj.keys else extObj.keys) ∧
      newHigh.keys=(if v.val ∈ highValid then insert v.val highObj.keys else highObj.keys) ∧
      newExt.mass ≤ extObj.mass+1 ∧ newHigh.mass ≤ highObj.mass+1 ∧
      ExteriorQueueMemory out.scalar.integerMemory out.scalar.core.mem width levelBase (levelBase+3) q domain extValid newExt.keys ∧
      newHigh.keys ⊆ domain.image Fin.val ∧ QueuedFlags out.scalar.integerMemory width (levelBase+6) domain newHigh.keys ∧
      Disjoint newHigh.cells newExt.cells ∧ st.scalar.core.ptrs 20 ≤ out.scalar.core.ptrs 20 ∧
      out.scalar.core.ptrs 20 ≤ st.scalar.core.ptrs 20+6 ∧
      (∀ z ∈ newExt.cells ∪ newHigh.cells, z < st.scalar.core.ptrs 20 → z ∈ extObj.cells ∪ highObj.cells) ∧
      (∀ other : Fin n, ∀ field < width, field ≠ levelBase+3 → field ≠ levelBase+6 →
        out.scalar.integerMemory (vertexRecordAddress width other.val field)=st.scalar.integerMemory (vertexRecordAddress width other.val field)) ∧
      (∀ z, 0 ≤ z → z < st.scalar.core.ptrs 20 → z ∉ extObj.cells ∪ highObj.cells → out.scalar.integerMemory z=st.scalar.integerMemory z) ∧
      out.scalar.core.mem=Function.update st.scalar.core.mem (vertexRecordAddress width v.val (levelBase+4))
        (if st.scalar.integerMemory (vertexRecordAddress width v.val (levelBase+2))=0 then 0 else
          if 3*theta*(st.scalar.integerMemory (vertexRecordAddress width v.val 0) : ℝ) ≤
            st.scalar.core.mem (vertexRecordAddress width v.val (levelBase+1)) then 1 else 0) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧
      out.scalar.halted=false ∧ out.scalar.core.ptrs 0=0 := by sorry
end NearlyOptimalPPR.Computation
