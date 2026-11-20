-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_exterior_numeric_prefix_exec
-- name    : NearlyOptimalPPR.Computation.exterior_numeric_prefix_exec
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:45:47.747186+00:00
-- url     : https://prove2.me/theorems/d43633a0-91d3-4789-8d4b-413ef7a9471e
-- title:
--   Exterior numeric prefix stores adjacency and updates all relevant residuals
-- statement:
--   Let an exterior vertex $v$ at level $j$ belong to the represented parent domain, and assume all active domains are nested correctly. Write $d=d_v$, $q$ for that level's threshold, $\rho(v)$ for its relative potential, and
--
--   $$\delta=\min\{r_j(v)/(5d),\;3q/8-\rho(v)\}.$$
--
--   The numeric prefix has a finite execution. It stores the adjacency row when needed, adds $\delta$ to the shared potential at $v$, and performs the prescribed self/budget and neighbor residual updates across open frames. The resulting graph cache covers the old stored set together with $v$. It returns the update scalars and the activation flag, which is set exactly when $\rho(v)+\delta=3q/8$. For top level $h$ and width $w$, the instruction count is at most
--
--   $$36w+161+(h+1)(4w+60)+d((h+1)(8w+39)+4w+31).$$
--
--   Output is preserved and charged work increases by that count. The exact degree/neighbor query count is also tracked, including the conditional cost of storing a new row.
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
theorem exterior_numeric_prefix_exec (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (logical : RecursiveState n) (s : Fin n) (α ε : ℝ) (ell length t : ℕ) (v : Fin n)
    (st : MachineState) (hh : st.scalar.halted=false)
    (pm : RecursiveMachineMemory g s α ε ell length logical st) (hDepth : logical.top ≤ ell)
    (ht : t ≤ logical.top) (hvDomain : v ∈ parentDomain logical t)
    (hSubset : ∀ i ≤ logical.top, (logical.frames i).active ⊆ parentDomain logical i)
    (hSelected : st.scalar.core.ptrs 112=(t : ℤ)) (hv : st.scalar.core.ptrs 40=(v.val : ℤ)) :
    let width := 16*(ell+3)
    let d := LocalPush.deg g.graph v
    let q := (logical.frames t).q
    let h := min ((logical.frames t).residual v/(5*d)) (3*q/8-relative logical t v)
    let endFree := if v ∈ logical.stored then st.scalar.core.ptrs 20 else st.scalar.core.ptrs 20+((g.neighbors v).length : ℤ)
    ∃ steps out, ∃ J : ℤ → ℤ, MachineEval m g ω exteriorNumericPrefixCode st steps out ∧
      steps ≤ 36*width+161+(logical.top+1)*(4*width+60)+
        (g.neighbors v).length*((logical.top+1)*(8*width+39)+4*width+31) ∧
      GraphCache g J width (insert v logical.stored) endFree ∧
      (∀ z, z ∉ cacheWriteCells width v.val (st.scalar.core.ptrs 20) (g.neighbors v).length → J z=st.scalar.integerMemory z) ∧
      (out.scalar.integerMemory,out.scalar.core.mem)=
        levelPayloadFold (storedNeighborMemoryUpdate g v logical ell ((1-α)*h)) 0 (g.neighbors v).length
          (J,levelRealMemoryFold (exteriorSelfBudgetMemoryUpdate J width v.val t (d*h) ((1-α)*d*h)) 0 (logical.top+1)
            (Function.update st.scalar.core.mem (vertexRecordAddress width v.val 0) (st.scalar.core.mem (vertexRecordAddress width v.val 0)+h))) ∧
      GraphCache g out.scalar.integerMemory width (insert v logical.stored) endFree ∧
      out.scalar.core.ptrs 20=endFree ∧ out.scalar.core.ptrs 40=(v.val : ℤ) ∧ out.scalar.core.ptrs 100=(logical.top : ℤ) ∧
      out.scalar.core.ptrs 120=((g.neighbors v).length : ℤ) ∧ out.scalar.core.ptrs 121=J (vertexRecordAddress width v.val 1) ∧
      out.scalar.core.ptrs 108=(logical.top : ℤ) ∧ out.scalar.core.ptrs 112=(t : ℤ) ∧ out.scalar.core.ptrs 116=(v.val : ℤ) ∧
      out.scalar.core.ptrs 114=(if relative logical t v+h=3*q/8 then 1 else 0) ∧
      out.scalar.core.regs 40=h ∧ out.scalar.core.regs 41=(1-α)*h ∧ out.scalar.core.regs 42=d*h ∧
      out.scalar.core.regs 43=q*d/2 ∧ out.scalar.core.regs 46=(1-α)*d*h ∧
      out.scalar.queries=st.scalar.queries+1+(if v ∈ logical.stored then 0 else (g.neighbors v).length+1)+(g.neighbors v).length ∧
      out.work=st.work+steps ∧ out.output=st.output ∧ out.scalar.halted=false ∧
      J (vertexRecordAddress width v.val 1)=(if v ∈ logical.stored then st.scalar.integerMemory (vertexRecordAddress width v.val 1) else st.scalar.core.ptrs 20) := by sorry
end NearlyOptimalPPR.Computation
