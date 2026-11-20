-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_exterior_activation_apply_exec
-- name    : NearlyOptimalPPR.Computation.exterior_activation_apply_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:45:56.487394+00:00
-- url     : https://prove2.me/theorems/79b929ed-4ace-4bfe-b674-7106514e6706
-- title:
--   Activation applies sparse list, child-record, and boundary transformations
-- statement:
--   Suppose the current active set is represented by an owned sparse vertex list and the selected source's cached row and root-membership bits are available. Assume the declared header, width, level, allocation-frontier, and list-separation conditions. The activation routine has a finite execution implementing the prescribed integer and real record transformations, prepending the source to the active list and allocating exactly three fresh integer cells. If $d$ is the source degree and $w$ the record width, then
--
--   $$t\le d(4w+19)+48w+279.$$
--
--   The routine updates the boundary count and any child activation fields according to the source operational definitions. It preserves graph-query count and output, increases charged work by exactly $t$, and returns the selected vertex and top-level register values. The resulting list occupies the union of the fresh node and the original owned footprint.
--
--   This contract isolates the activation bookkeeping from numeric propagation and subsequent queue restoration.
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
theorem exterior_activation_apply_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (st : MachineState) (hh : st.scalar.halted=false) (source : Fin n) (rootActive : Finset (Fin n))
    (boundary level top width : ℕ) (free base : ℤ) (opened : Bool)
    (vertices : List (Fin n)) (F : Finset ℤ)
    (hWidth : level < top → 16*(level+1)+22 < width)
    (h0 : st.scalar.core.ptrs 0=0) (h50 : st.scalar.core.ptrs 50=(width : ℤ))
    (h108 : st.scalar.core.ptrs 108=(top : ℤ)) (h112 : st.scalar.core.ptrs 112=(level : ℤ))
    (h116 : st.scalar.core.ptrs 116=(source.val : ℤ)) (h40 : st.scalar.core.ptrs 40=(source.val : ℤ))
    (h120 : st.scalar.core.ptrs 120=((g.neighbors source).length : ℤ)) (h121 : st.scalar.core.ptrs 121=base)
    (h20 : st.scalar.core.ptrs 20=free) (hOne : st.scalar.core.regs 31=1)
    (hFree : 128+32*((level+1 : ℕ) : ℤ) ≤ free)
    (hBoundary : st.scalar.integerMemory 7=(boundary : ℤ))
    (hOpen : st.scalar.integerMemory (levelHeaderAddress level 9)=(if opened then 1 else 0))
    (hRep : VertexListRep st.scalar.integerMemory (st.scalar.integerMemory (levelHeaderAddress level 1)) vertices F)
    (hBelow : ∀ z ∈ F, z < free) (hAbove : ∀ z ∈ F, 128+32*((level+1 : ℕ) : ℤ) ≤ z)
    (hRow : ∀ (i : ℕ) (hi : i < (g.neighbors source).length), st.scalar.integerMemory (base+(i : ℤ))=(((g.neighbors source)[i]'hi).val : ℤ))
    (hRootActive : level=0 → ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress width v.val 18)=(if v ∈ rootActive then 1 else 0)) :
    ∃ steps out, MachineEval m g ω exteriorActivationApplyCode st steps out ∧
      steps ≤ (g.neighbors source).length*(4*width+19)+48*width+279 ∧
      out.scalar.core.ptrs 100=(top : ℤ) ∧ out.scalar.core.ptrs 20=free+3 ∧ out.scalar.core.ptrs 0=0 ∧
      out.scalar.integerMemory=exteriorActivationIntegerMemory g source rootActive boundary level top width free st.scalar.integerMemory ∧
      out.scalar.core.mem=exteriorActivationRealMemory st.scalar.core.mem source.val level top width (st.scalar.core.regs 43) opened ∧
      VertexListRep out.scalar.integerMemory (out.scalar.integerMemory (levelHeaderAddress level 1)) (source::vertices) (nodeCells free ∪ F) ∧
      (∀ z ∈ nodeCells free ∪ F, z < free+3) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      out.scalar.core.ptrs 40=(source.val : ℤ) := by sorry
end NearlyOptimalPPR.Computation
