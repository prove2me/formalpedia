-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_fresh_child_simulation
-- name    : NearlyOptimalPPR.Computation.fresh_child_simulation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:42.147179+00:00
-- url     : https://prove2.me/theorems/1e46531b-fe2c-4c86-9dad-cf53fcce061b
-- title:
--   Charged child-call preparation preserves ancestor frames
-- statement:
--   Suppose a represented recursive state has top level $h<\ell$, a positive block parameter, and an active set contained in both the stored vertices and its parent domain. Assume the child allocation capacity covers the represented active list and is below $2^r$, with queue-array length greater than $r$. The fresh-child routine has a finite execution representing the source child-spawn transition. If $a$ is the active-list length, then
--
--   $$M'\le M+a.$$
--
--   The instruction bound is the charged block-search cost plus the explicit rank-array initialization and per-active-vertex preparation costs in the interface. The routine makes no graph query, preserves existing output and every solve-epoch mark, and leaves all represented ancestor frames valid.
--
--   This result accounts for parameter searches and sparse child initialization rather than granting a free child-state constructor.
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
theorem fresh_child_simulation (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length capacity rank : ℕ)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st)
    (hDepth : logical.top < ell)
    (hStored : (logical.frames logical.top).active ⊆ logical.stored)
    (hRegion : (logical.frames logical.top).active ⊆ parentDomain logical logical.top)
    (hBlock : 1 ≤ (logical.frames logical.top).block)
    (hBudget : ((pm.frames logical.top (le_refl _)).activeVertices).length ≤ capacity)
    (hcap : rank < length) (hpow : capacity < 2^rank) :
    ∃ steps out, ∃ memory : RecursiveMachineMemory g s α ε ell length (spawnChildState g ell logical) out,
      MachineEval m g ω freshChildCode st steps out ∧
      memory.queueMass ≤ pm.queueMass+((pm.frames logical.top (le_refl _)).activeVertices).length ∧
      steps ≤ ((logical.frames logical.top).block+2)*(4*(ell-(logical.top+1))+22)+10*length+324+
        ((pm.frames logical.top (le_refl _)).activeVertices).length*(21*rank+60*(16*(ell+3))+190) ∧
      out.scalar.queries=st.scalar.queries ∧ out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      (∀ v : Fin n, out.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)=
        st.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 7)) := by sorry
end NearlyOptimalPPR.Computation
