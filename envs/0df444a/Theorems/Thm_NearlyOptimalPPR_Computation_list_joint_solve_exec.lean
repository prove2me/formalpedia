-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_list_joint_solve_exec
-- name    : NearlyOptimalPPR.Computation.list_joint_solve_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:30.671761+00:00
-- url     : https://prove2.me/theorems/38ce7812-24de-42b7-b6b4-1ca49025fe4f
-- title:
--   List-based sparse joint solve and charged enumeration
-- statement:
--   Let $C$ be represented by a nonempty duplicate-free owned list of stored positive-degree vertices, with $0<\alpha<1$ and a represented right-hand side $b$. Assume valid recursive keys and domains, bounded epoch marks, the allocation separation conditions, and sufficient queue capacity. Put
--
--   $$S=\operatorname{vol}(C)+|C|,\qquad y=M_C^{-1}b_C.$$
--
--   The list-based routine terminates in a finite instruction execution and represents the joint potential update by $y$, followed by touched-vertex key refresh. In addition to the cached-solve assembly and refresh costs, it pays $10|C|+5$ instructions to construct the enumeration. Heap mass increases by at most $2(h+1)S$. Output is preserved, and the solve epoch advances by one with all marks bounded by it.
--
--   The theorem supplies the charged bridge from a sparse vertex list to the cached exact-solve interface; no graph-wide scan is assumed.
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
theorem list_joint_solve_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length N rank offset : ℕ)
    (vertices : List (Fin n)) (head epoch : ℤ) (F : Finset ℤ)
    (hNodup : vertices.Nodup) (hNonempty : 0<vertices.length)
    (hd : ∀ v ∈ vertices, 0<g.graph.degree v) (hα : 0<α ∧ α<1) (b : Fin n → ℝ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (hmem : ∀ v ∈ vertices, v ∈ logical.stored)
    (hhp : st.scalar.core.ptrs 90=head)
    (hList : VertexListRep st.scalar.integerMemory head vertices F)
    (hBelow : ∀ z ∈ F, z < st.scalar.core.ptrs 20)
    (hE : st.scalar.core.ptrs 53=epoch) (hOff : st.scalar.core.ptrs 83=(offset : ℤ))
    (hbRecords : ∀ v ∈ vertices, st.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val offset)=b v)
    (hbound : ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch)
    (hKeys : KeysInvariant g logical)
    (hSubset : ∀ j ≤ logical.top, (logical.frames j).active ⊆ parentDomain logical j)
    (hMass : pm.queueMass+2*(logical.top+1)*(volumeNat g vertices.toFinset+vertices.toFinset.card) ≤ N)
    (hCap : rank < length) (hPow : N < 2^rank) :
    let size := volumeNat g vertices.toFinset+vertices.toFinset.card
    let numericCost := (24*(16*(ell+3))+100)*size+28
    let updateCost := jointSolveIterationFactor ell logical.top rank*size+5
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length
      (refreshKeys g (jointUpdate g α logical (solveOn g α vertices.toFinset b)) (touchedBy g vertices.toFinset)) out,
      MachineEval m g ω listJointSolveCode st steps out ∧
      steps ≤ (10*vertices.length+5)+numericCost+updateCost+1 ∧
      memory.queueMass ≤ pm.queueMass+2*(logical.top+1)*size ∧
      out.work ≤ st.work+((10*vertices.length+5)+numericCost+updateCost : ℕ)+
        solveCharge m vertices.length (principalEntries g α (vertexEnumeration vertices)).length ∧
      out.output=st.output ∧ out.scalar.halted=false ∧
      (out.scalar.core.ptrs 53=epoch+1 ∧ ∀ v : Fin n,
        out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7) ≤ epoch+1) := by sorry
end NearlyOptimalPPR.Computation
