-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_exterior_activation_raw_exec
-- name    : NearlyOptimalPPR.Computation.exterior_activation_raw_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:45:54.914195+00:00
-- url     : https://prove2.me/theorems/fb701be2-ee26-4286-8633-e1fdd6d61784
-- title:
--   Numeric propagation followed by activation has the source raw memory effect
-- statement:
--   Assume a represented exterior selection reaches the activation threshold after its source update, with valid parent-domain nesting and a represented nonnegative boundary counter. Let $d$ be the selected vertex's degree, $h$ the current top level, and $w=16(\ell+3)$ the record width. The complete numeric-and-activation prefix has a finite execution with
--
--   $$t\le84w+442+(h+1)(4w+60)+d((h+1)(8w+39)+8w+50).$$
--
--   Its numeric payload is exactly the prescribed exterior residual/potential update followed by the activation record transformations. Its graph cache covers the enlarged stored set, and the selected level's list is the source prepended to its old active list, using three fresh cells after any newly stored adjacency row. Output is preserved and charged work increases by $t$. The degree/neighbor query count is tracked exactly.
--
--   The result describes the intermediate numeric and activation state before restoring queue coverage; that restoration is supplied separately by the touched-refresh theorem.
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
theorem exterior_activation_raw_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length t boundary : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (ht : t ≤ logical.top) (hvDomain : v ∈ parentDomain logical t)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hSelected : st.scalar.core.ptrs 112=(t : ℤ)) (hv : st.scalar.core.ptrs 40=(v.val : ℤ))
    (hBoundary : logical.boundaryEdges=(boundary : ℤ))
    (hAdmit : relative logical t v+compilerExteriorDelta g α logical t v=3*(logical.frames t).q/8) :
    let width := 16*(ell+3)
    let δ := compilerExteriorDelta g α logical t v
    let free := if v ∈ logical.stored then st.scalar.core.ptrs 20 else st.scalar.core.ptrs 20+((g.neighbors v).length : ℤ)
    ∃ steps out, ∃ J : ℤ → ℤ,
      MachineEval m g ω exteriorNumericRawCode st steps out ∧
      steps ≤ 84*width+442+(logical.top+1)*(4*width+60)+
        (g.neighbors v).length*((logical.top+1)*(8*width+39)+8*width+50) ∧
      GraphCache g J width (insert v logical.stored) free ∧
      (∀ z, z ∉ cacheWriteCells width v.val (st.scalar.core.ptrs 20) (g.neighbors v).length → J z=st.scalar.integerMemory z) ∧
      J (vertexRecordAddress width v.val 1)=(if v ∈ logical.stored then st.scalar.integerMemory (vertexRecordAddress width v.val 1) else st.scalar.core.ptrs 20) ∧
      out.scalar.integerMemory=exteriorActivationIntegerMemory g v (logical.frames 0).active boundary t logical.top width free
        (exteriorNumericPayload g logical ell α t v δ J st.scalar.core.mem).1 ∧
      out.scalar.core.mem=exteriorActivationRealMemory (exteriorNumericPayload g logical ell α t v δ J st.scalar.core.mem).2
        v.val t logical.top width ((logical.frames t).q*LocalPush.deg g.graph v/2) (logical.frames t).openBudget ∧
      VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress t 1))
        (v::(pm.frames t ht).activeVertices) (nodeCells free ∪ (pm.frames t ht).activeFoot) ∧
      (∀ z ∈ nodeCells free ∪ (pm.frames t ht).activeFoot, z < free+3) ∧
      out.scalar.core.ptrs 20=free+3 ∧ out.scalar.core.ptrs 100=(logical.top : ℤ) ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.core.ptrs 116=(v.val : ℤ) ∧
      out.scalar.core.ptrs 120=((g.neighbors v).length : ℤ) ∧
      out.scalar.queries=st.scalar.queries+1+(if v ∈ logical.stored then 0 else (g.neighbors v).length+1)+(g.neighbors v).length ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false := by sorry
end NearlyOptimalPPR.Computation
