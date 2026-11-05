-- Prove2me | Theorems.Thm_HardyFLocal_lattice_probabilities_well_defined
-- name    : HardyFLocal.lattice_probabilities_well_defined
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:23.80813+00:00
-- url     : https://prove2.me/theorems/cfac9a8f-5a0f-4301-ab89-31d3369c3459
-- title:
--   Eq. (6), p.8 — the lattice probabilities are well defined
-- statement:
--   Let $\rho$ be a density matrix on the $m+n$ qubits of the lattice. For every total label $t$ the lattice probability is nonnegative, and for every setting $F$
--   $$\sum_{Y}\mathrm{prob}(Y\mid F)=1,$$
--   as an unconditional sum over the families of outcomes under $F$. So the lattice probabilities form an experiment model.
--
--   The paper assumes (6) in general, "glossing over subtle points", and this is the assumption for the setting of its §5. It makes the hypotheses of the mission's goal satisfiable.
--
--   Differences from the source:
--   - reading: "a large number" of qubits → every m, n in ℕ, including small ones; reason: the statement is uniform in the lattice size and states nothing different on small lattices
--   - encoding: the labelling sentence of p.12 has v running from right to left → on a right mover (u, v) is followed by (u, v+1), on a left mover (u, v) by (u+1, v); reason: the explicit statement of p.13; it differs only by reversing both labellings
--   - reading: superoperators are "trace non-increasing maps on density operators that take allowed states to allowed states" → completely positive (finite Kraus form) and trace non-increasing; reason: the standard meaning; positivity alone fails on entangled inputs, which this lattice produces
--   - reading: "a general measurement" with a display panel, with no outcome count → an instrument with branches indexed by ℕ, zero branches allowed, HasSum normalization; reason: covers every finite instrument; the stronger reading, which adds the summability clause
--   - reading: the paper names no initial state → every density matrix on all the qubits, fixed once for the model; reason: entangled or not; the claim is uniform in it
--   - encoding: labels run from 1, and the first element of Ω² is 1 → labels are 0-based, and the first element of Ω² = Fin 16 is 0; reason: Lean convention; same instances
--   - encoding: no order of evaluation is named across incomparable vertices → boxes are applied in lexicographic order; reason: lexicographic order extends the order along every qubit, and boxes sharing no qubit commute (proved in the verification file), so any other extension gives the same number
--   - encoding: the probability is the trace of the state after all the boxes → the real part of that trace (latticeProb); reason: the trace is real on the positive semidefinite matrices the boxes produce; same values
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §4.2, eq. (6), p.8; §5, p.12

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Fiducial
import Definitions.Def_HardyCausaloid_Causaloid
import Definitions.Def_HardyCausaloid_Conditional
import Definitions.Def_HardyFLocal_Superoperator
import Definitions.Def_HardyFLocal_Instrument
import Definitions.Def_HardyFLocal_Lattice
import Definitions.Def_HardyFLocal_FiducialFamily
import Definitions.Def_HardyFLocal_ClumpCausaloid

set_option autoImplicit false

namespace HardyFLocal

open HardyCausaloid

/-- **The lattice probabilities are well defined**, Hardy, *Formalism Locality in Quantum Theory
and Quantum Gravity*, arXiv:0804.0054v1, §4.2, eq. (6), p.8 ("We will assume that the probabilities
prob(Y_V|F_V) are well defined"), for the qubit lattice of §5, p.12.

For every density matrix `ρ` on all the qubits, the lattice probability is nonnegative, sums to `1`
over the outcome families of every setting `F`, and so is an experiment model.

**Formalization Note** The sum is unconditional, over all families of natural-number outcomes; zero
branches pad a finite instrument. -/
theorem lattice_probabilities_well_defined {m n : ℕ} (ρ : GlobalMat m n) (hρ : IsDensity ρ) :
    (∀ t : (∀ x, Label (Setting m n) (Outcome m n) x), 0 ≤ latticeProb ρ t) ∧
    (∀ F : (∀ x : X m n, Setting m n x),
      HasSum (fun Y : (∀ x, Outcome m n x (F x)) => latticeProb ρ fun x => ⟨F x, Y x⟩) 1) ∧
    ∃ M : Model (Setting m n) (Outcome m n), IsLatticeModel ρ M := by sorry

end HardyFLocal
