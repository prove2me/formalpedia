-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_root_sparse_output_exec
-- name    : NearlyOptimalPPR.Computation.root_sparse_output_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:33.173077+00:00
-- url     : https://prove2.me/theorems/f8f067e8-3aec-4867-ba8f-bdfd2cc2322c
-- title:
--   Charged sparse emission of the pruned root potential
-- statement:
--   Let $A$ be the represented root active set and suppose the pruned potential vanishes outside $A$. The root sparse-output routine terminates after exactly
--
--   $$t=(8w+31)|A|+10,\qquad w=16(\ell+3),$$
--
--   instructions and its explicit output denotes $\alpha D(x-3q/8)_+$, where $x$ is the shared potential and $q$ is the root threshold. Charged work increases by exactly $t$. Integer memory, real memory, and the graph-query count are preserved, and the machine remains ready to continue.
--
--   The routine walks the stored active list and makes no dense final graph scan. The vanishing hypothesis ensures that omitted vertices have the intended zero output.
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
theorem root_sparse_output_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hStored : (logical.frames 0).active ⊆ logical.stored)
    (hOutside : ∀ v ∉ (logical.frames 0).active, prune (logical.frames 0).q logical.x v=0) :
    ∃ out, MachineEval m g ω rootSparseOutputCode st
      ((8*(16*(ell+3))+31)*(logical.frames 0).active.card+10) out ∧
      outputVector out.output=potentialOutput g.graph α (prune (logical.frames 0).q logical.x) ∧
      out.work=st.work+((8*(16*(ell+3))+31)*(logical.frames 0).active.card+10 : ℕ) ∧
      out.scalar.integerMemory=st.scalar.integerMemory ∧ out.scalar.core.mem=st.scalar.core.mem ∧
      out.scalar.queries=st.scalar.queries ∧ out.scalar.halted=false := by sorry
end NearlyOptimalPPR.Computation
