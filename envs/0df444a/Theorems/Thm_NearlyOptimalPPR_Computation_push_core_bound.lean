-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_push_core_bound
-- name    : NearlyOptimalPPR.Computation.push_core_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:31.0307+00:00
-- url     : https://prove2.me/theorems/0c3f9e52-9a4b-4e98-b9f5-67d2896a629a
-- title:
--   Actual sparse Push implementation has charged ACL work bound
-- statement:
--   For every fixed solve model there is a positive constant $C$ such that, on a nonisolated seed with $0<\alpha<1$ and $0<\varepsilon\le1$, the sparse Push core has a finite execution from the specified constant-size input layout and initially empty output. It produces a nonnegative vector $p$ with
--
--   $$|p(v)-\pi_s(v)|\le\varepsilon d_v,\qquad t\le C/(\alpha\varepsilon).$$
--
--   Here $t$ is the instruction count and exactly the increase in charged machine work. Both negative-address memories start at zero; the seed, teleportation parameter, and tolerance occupy the declared input cells. The machine remains ready to continue after the output is emitted.
--
--   This theorem implements the source Push guarantee with actual degree/neighbor queries, sparse FIFO and support lists, and charged explicit output.
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
theorem push_core_bound (m : SolveModel) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ω : ℕ → Bool)
      (st : MachineState), 0 < α → α < 1 → 0 < ε → ε ≤ 1 → 0 < g.graph.degree s →
      st.scalar.halted=false → st.scalar.integerMemory 0=(s.val : ℤ) → st.scalar.core.mem 0=α → st.scalar.core.mem 1=ε →
      (∀ z, z < 0 → st.scalar.integerMemory z=0) → (∀ z, z < 0 → st.scalar.core.mem z=0) → st.output=[] →
      ∃ steps out, MachineEval m g ω pushCoreCode st steps out ∧
        (steps : ℝ≥0∞) ≤ ENNReal.ofReal (C/(α*ε)) ∧
        ACL g.graph α ε s (outputVector out.output) ∧ (∀ v : Fin n, 0 ≤ outputVector out.output v) ∧
        out.work=st.work+steps ∧ out.scalar.halted=false := by sorry
end NearlyOptimalPPR.Computation
