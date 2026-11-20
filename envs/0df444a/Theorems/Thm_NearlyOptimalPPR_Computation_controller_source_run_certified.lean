-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_controller_source_run_certified
-- name    : NearlyOptimalPPR.Computation.controller_source_run_certified
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-19T06:24:37.824751+00:00
-- url     : https://prove2.me/theorems/7418bbdc-4736-41ea-8901-8fde13fca6fa
-- title:
--   Source running-time bound transfers to actual recursive-controller execution
-- statement:
--   Suppose $0<\alpha\le1/2$, $0<\varepsilon\le1$, and the seed has positive degree. Assume the canonical recursive source run has a finite terminal prefix and source work at most $E$. Let a prepared concrete root represent its initial state with heap mass at most one. Choose queue capacity $N$, rank $r$, and array length $L$ with
--
--   $$8(\ell+1)E\le N<2^r,\qquad r<L,$$
--
--   and sufficient cache-potential credit. Then the actual recursive controller has a finite execution, producing a nonnegative ACL-accurate explicit output. Its charged work is at most
--
--   $$W_{\rm initial}+P+F E+1,$$
--
--   where $P$ is the heap-cleaning coefficient and $F$ the explicit compiler overhead factor. The source termination and work hypotheses are discharged separately when this transfer theorem is applied to the uniform algorithm.
--
--   The result derives all reachable allocation bounds and instruction charges from source finite-prefix invariants.
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
theorem controller_source_run_certified (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (s : Fin n) (α ε E : ℝ) (ell length N rank Q : ℕ)
    (hα : 0<α ∧ α≤1/2) (hε : 0<ε ∧ ε≤1) (hs : 0<g.graph.degree s)
    (hBound : recursiveWork m g s α ε ell [] ≤ ENNReal.ofReal E)
    (hWide : ((8*(ell+1) : ℕ) : ℝ≥0∞)*ENNReal.ofReal E ≤ (N : ℝ≥0∞))
    (hTermination : ∃ t, (recursiveRun m g s α (rootThreshold ε ell) ell [] t).done=true)
    (hCredit : 4*(16*(ell+3))+17 ≤ Q) (hCap : rank<length) (hPow : N<2^rank)
    (st : MachineState) (memory : ControllerMemory g s α ε ell length
      (recursiveInit g s (rootThreshold ε ell) ell []) st) (hM : memory.mass ≤ 1) :
    let P := cleanBodyBound (16*(ell+3)) length rank+2
    let F := compilerOverheadFactor ell length rank Q
    ∃ steps out, MachineEval m g ω recursiveControllerCode st steps out ∧
      (∀ v : Fin n, 0 ≤ outputVector out.output v) ∧ ACL g.graph α ε s (outputVector out.output) ∧
      out.work ≤ st.work+(P : ℝ≥0∞)+(F : ℝ≥0∞)*ENNReal.ofReal E+1 := by sorry
end NearlyOptimalPPR.Computation
