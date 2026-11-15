-- Prove2me | Theorems.Thm_LindbladQueryOptimal_Simulation_Supplement_theorem_9
-- name    : LindbladQueryOptimal.Simulation.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:12:59.110195+00:00
-- url     : https://prove2.me/theorems/f8bffe9d-ea19-4ae7-a588-a63894b49178
-- title:
--   Theorem 9 — Simulation of a Single Jump Operator
-- statement:
--   Let $L$ be an arbitrary operator on an $n$-qubit system, and let $O_L$ be an exact $\alpha$-block encoding of $L$ on $a$ qubits, with $a\ge n$, $a>0$ and $\alpha>0$, using the zero-padding embeddings of Definition 2. There is no Hamiltonian term and there is exactly one jump operator. Write
--   $$
--   D_L(X)=LXL^\dagger-\tfrac12(L^\dagger LX+XL^\dagger L),\qquad \tau=t\alpha^2.
--   $$
--   For every $t\ge0$ and $0<\epsilon\le1/2$, controlled access to $O_L$ and $O_L^\dagger$ suffices to implement a completely positive trace-preserving channel $\widetilde\Phi$ satisfying the entire equality and bound
--   $$
--   \|\widetilde\Phi-\exp(tD_L)\|_\diamond
--   =\|\widetilde\Phi-\exp(\tau D_{L/\alpha})\|_\diamond\le\epsilon.
--   $$
--   There is a positive absolute constant $C_{\rm query}$, independent of all dimensions, widths, normalizations, times, precisions and oracle matrices, such that the total number of forward, adjoint and controlled oracle calls is at most $C_{\rm query}c(\tau,\epsilon)$, where
--   $$
--   c(\tau,\epsilon)=1+\tau+\frac{\log(1/\epsilon)}{\log(e+\log(1/\epsilon)/\tau)}\quad(\tau>0),\qquad c(0,\epsilon)=1.
--   $$
--   The same circuit has this query bound and induces the stated channel. Its ordinary gates are chosen from the known parameters before the unknown matrices $L,O_L$; the circuit has one oracle slot and uses arbitrary one- and two-qubit ordinary gates. All work qubits start in zero and are discarded at the output, retaining every success and failure outcome. No gate-complexity assertion or catalyst preparation assumption is added. At zero time the identity channel with no oracle calls is available.
--
--   This is the single-jump companion theorem to the retained general-simulation goal. Its numbered supporting results are already published in the base mission and are not posed again.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert spaces and exact zero-padded block encodings → complex matrices indexed by Bits n and blockEncoding α 0 OL L on a positive-width register; reason: coordinates for precisely Definition 2 and the arbitrary square jump operator of §3
--   - encoding: a channel implementable using controlled access to the jump oracle and its adjoint → one-slot OracleCircuit selected before L and OL, with circuitChannel and the combined oracleCount; reason: exposes oracle independence and actual full discarded-work channel semantics without imposing a gate bound
--   - encoding: O(c(τ,ε)) total forward or adjoint queries → one positive real Cquery before every instance, with oracleCount ≤ Cquery * queryScale (t * α^2) ε; reason: exact uniform big-O meaning supplied by §3.6; no numerical constant is asserted
--   - encoding: unhalved diamond norms bounded by the positive real ε → the published extended-nonnegative diamond norm bounded by ENNReal.ofReal ε; reason: same finite norm on the linear maps here, without a default-valued real supremum
-- source:
--   Chunhao Wang, Christopher Ye, Query-optimal quantum simulation of Lindblad evolution, STOC 2027 submission #1077 (October 2026), Theorem 9, p. 12, Eqs. (33)–(35); standing model: Definition 2, p. 6 and §3, p. 12; proof §§3.1–3.6, pp. 12–26. Canonical source: papers/stoc2027-1077/source.pdf (SHA256 51bc866a7111a7e6819f49360208fcdfd52f7fd24464cf015db99d40543d5d88).

import Definitions.Def_LindbladQueryOptimal_Simulation_Circuits

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace LindbladQueryOptimal.Simulation.Supplement

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Wang--Ye, Theorem 9, p. 12, Eqs. (33)--(35). One oracle slot;
forward, adjoint and controlled calls contribute to the same counter.
The circuit is chosen before the unknown jump and its block encoding. -/
theorem theorem_9 :
    ∃ Cquery : ℝ, 0 < Cquery ∧
    ∀ (n a : ℕ), n ≤ a → 0 < a →
    ∀ (α t ε : ℝ), 0 < α → 0 ≤ t → 0 < ε → ε ≤ 1/2 →
    ∃ C : OracleCircuit n 1 (fun _ => a),
      (oracleCount C.gates 0 : ℝ) ≤ Cquery * queryScale (t * α ^ 2) ε ∧
      ∀ (L : Op (Bits n)) (OL : Op (Bits a)), blockEncoding α 0 OL L →
        let Φ := circuitChannel C (fun _ : Fin 1 => OL)
        channel Φ ∧
        RandomDimReduction.Channel.diamond (fun X => Φ X - dissipativeEvolution L t X) =
          RandomDimReduction.Channel.diamond (fun X => Φ X -
            dissipativeEvolution ((α : ℂ)⁻¹ • L) (t * α ^ 2) X) ∧
        RandomDimReduction.Channel.diamond (fun X => Φ X -
          dissipativeEvolution ((α : ℂ)⁻¹ • L) (t * α ^ 2) X) ≤ ENNReal.ofReal ε := by sorry

end LindbladQueryOptimal.Simulation.Supplement
