-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_theorem_19
-- name    : LindbladQueryOptimal.Simulation.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:11.329961+00:00
-- url     : https://prove2.me/theorems/516a0446-2fef-400c-b5ae-376f4cb0f1c0
-- title:
--   Theorem 19 — Lindblad simulation with optimal queries and nearly optimal gates
-- statement:
--   There are positive absolute constants $C_q,C_g,C_a$, independent of every register size, oracle, normalization, time and precision, with the following property. Let $H$ be Hermitian on an $n$-qubit system and let $L_1,\ldots,L_m$ be arbitrary system operators. Their input oracles are exact block encodings with positive known normalizations $\alpha_H,\alpha_1,\ldots,\alpha_m$, and controlled access and controlled adjoints are available. Set $M=\alpha_H+\sum_j\alpha_j^2$, $\tau=tM$, and
--   $$c(\tau,\epsilon)=1+\tau+\frac{\log(1/\epsilon)}{\log(e+\log(1/\epsilon)/\tau)},\qquad c(0,\epsilon)=1.$$
--   For $t>0$ and $0<\epsilon\le1/2$, there is an oracle-independent circuit whose full mixed-output CPTP channel $\Phi_{\rm sim}$ satisfies
--   $$\|\Phi_{\rm sim}-\exp(t\mathcal L)\|_\diamond\le\epsilon,$$
--   where $\mathcal L(X)=-i(HX-XH)+\sum_j(L_jXL_j^\dagger-\tfrac12(L_j^\dagger L_jX+XL_j^\dagger L_j))$. It uses at most $C_qc(\tau,\epsilon)$ calls to each input oracle, counting forward/inverse and controlled calls together, and at most
--   $$C_gc(\tau,\epsilon)\left[C_{\rm anc}+m+\log\!\left(e+\frac{\tau+1}{\epsilon}\right)\log\!\left(e+\frac{(m+1)(\tau+1)}{\epsilon}\right)\right]$$
--   additional arbitrary one-/two-qubit gates. Both counters and the error concern the same circuit. Its work starts in zero and is fully discarded, retaining the system also on failure outputs.
--
--   For the standard zero-padding embeddings, clean elementary range-test circuits exist with total cost at most $C_a\sum_A(1+a_A-n)$, where $a_A$ is each encoding-register size. For any supplied such circuits, $C_{\rm anc}$ in the bound is their actual total elementary-gate count. They toggle the public/private flag on the zero-ancilla sector and support its fixed embedding operations; the same system wires represent the system in both branches. The simulator is selected from these known routines, register data, scalar normalizations, $t$ and $\epsilon$ before all unknown oracle matrices, $H$ and $L_j$. Empty jump families use only Hamiltonian access.
--
--   Differences from the source:
--   - encoding: finite-dimensional complex Hilbert operators and direct sums → complex matrices indexed by finite types and sum types; reason: coordinate representation preserves every source instance and the spectral norm
--   - encoding: unhalved diamond error and universal O query/gate constants → the published ENNReal diamond norm and positive constants quantified before every instance; reason: the unit-ball norm equals the source norm on these linear maps; uniform existential constants express exactly the source O bounds
--   - encoding: C_anc includes range membership tests and associated fixed embedding operations and is linear for standard embeddings → actual elementary-gate counters of clean flag-test circuits, universal linear-size existence, and common-system-wire zero-sector identifications; reason: a concrete physical implementation of the standard padding embeddings; constant-cost branch rotations are absorbed in the same absolute gate constant
--   - encoding: an algorithm using controlled input oracles and their adjoints → a circuit selected before the unknown matrices, with combined forward/adjoint per-oracle counters and full discarded-work semantics; reason: makes oracle independence, per-oracle resource usage and the CPTP failure completion explicit without postselection
-- source:
--   Chunhao Wang, Christopher Ye, STOC 2027 submission #1077 (October 2026), Theorem 19, pp. 26–27; standard embedding cost and gate proof §§4.3.2–4.3.5, pp. 35–40; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1077.pdf

import Definitions.Def_LindbladQueryOptimal_Simulation_Circuits
import Definitions.Def_LindbladQueryOptimal_Simulation_Local

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem theorem_19 : ∃ Cquery Cgate Canc : ℝ,
    0 < Cquery ∧ 0 < Cgate ∧ 0 < Canc ∧
    ∀ (n m aH : ℕ) (a : Fin m → ℕ),
      n ≤ aH → (∀ j, n ≤ a j) → 0 < aH → (∀ j, 0 < a j) →
      (∃ R : AncillaRoutines n (m+1) (inputWidth aH a),
        validRoutines R ∧ (ancillaCost R : ℝ) ≤
          Canc * ∑ j, ((inputWidth aH a j - n + 1 : ℕ) : ℝ)) ∧
      (∀ (R : AncillaRoutines n (m+1) (inputWidth aH a)), validRoutines R →
        ∀ (αH : ℝ) (α : Fin m → ℝ) (t ε : ℝ),
          0 < αH → (∀ j, 0 < α j) → 0 < t → 0 < ε → ε ≤ 1/2 →
          ∃ C : OracleCircuit n (m+1) (inputWidth aH a),
            (∀ j, (oracleCount C.gates j : ℝ) ≤
              Cquery * queryScale (t * normalization αH α) ε) ∧
            (elementaryCount C.gates : ℝ) ≤
              Cgate * gateScale (t * normalization αH α) ε m (ancillaCost R) ∧
            ∀ (H : Op (Bits n)) (L : Fin m → Op (Bits n))
              (OH : Op (Bits aH)) (OL : ∀ j, Op (Bits (a j))),
              Hᴴ = H → exactAccess H αH OH (padding n aH) (padding n aH) →
              (∀ j, exactAccess (L j) (α j) (OL j) (padding n (a j)) (padding n (a j))) →
              channel (circuitChannel C (inputOracles OH OL)) ∧
              RandomDimReduction.Channel.diamond (fun X =>
                circuitChannel C (inputOracles OH OL) X - evolution H L t X) ≤
                ENNReal.ofReal ε) := by sorry

end LindbladQueryOptimal.Simulation
