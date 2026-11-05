-- Prove2me | Theorems.Thm_HardyFLocal_clumping_computes_probabilities
-- name    : HardyFLocal.clumping_computes_probabilities
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:16.701423+00:00
-- url     : https://prove2.me/theorems/335865e7-e210-4349-a295-6240b451add4
-- title:
--   Clumping steps 1–3, p.14 — the method computes every probability of every region
-- statement:
--   Let $\rho$ be a density matrix on the qubits, $M$ the model of the lattice, $\$_k$ a fiducial family, $L$ fiducial labels and $C$ the causaloid of the lattice. For every finite set $O$ of vertices, every label $\alpha$ of the region $R_O$ and every generalized preparation $s$ outside it,
--   $$p_\alpha=\mathbf r_\alpha(R_O)\cdot\mathbf p(R_O),$$
--   where $\mathbf p(R_O)$ lists the probabilities of the labels in $\Omega_C(O)$ under $s$, and $\mathbf r_\alpha(R_O)$ is computed from the causaloid: from the elementary table of $\alpha$ and the $\Lambda$ matrix of the clumps.
--
--   This holds at every region, and it is the claim that the method gives the right matrix.
--
--   Differences from the source:
--   - reading: "a large number" of qubits → every m, n in ℕ, including small ones; reason: the statement is uniform in the lattice size and states nothing different on small lattices
--   - encoding: the labelling sentence of p.12 has v running from right to left → on a right mover (u, v) is followed by (u, v+1), on a left mover (u, v) by (u+1, v); reason: the explicit statement of p.13; it differs only by reversing both labellings
--   - reading: superoperators are "trace non-increasing maps on density operators that take allowed states to allowed states" → completely positive (finite Kraus form) and trace non-increasing; reason: the standard meaning; positivity alone fails on entangled inputs, which this lattice produces
--   - reading: "a general measurement" with a display panel, with no outcome count → an instrument with branches indexed by ℕ, zero branches allowed, HasSum normalization; reason: covers every finite instrument; the stronger reading, which adds the summability clause
--   - reading: the paper names no initial state → every density matrix on all the qubits, fixed once for the model; reason: entangled or not; the claim is uniform in it
--   - reading: a "fiducial spanning set of superoperators", with Λ in "a real vector space" (p.9) → a basis over ℝ of the Hermiticity-preserving one-qubit maps; reason: real coefficients are what p.9 requires, and they exist for Hermiticity-preserving maps
--   - reading: (21)–(22) take k′, k″ in {1} and k in Ω² → the earliest vertex of a clump carries the free label, later vertices the label 1, on each of the two qubits of a vertex; reason: this is the index placement of (21)–(22) applied to every clump
--   - encoding: labels run from 1, and the first element of Ω² is 1 → labels are 0-based, and the first element of Ω² = Fin 16 is 0; reason: Lean convention; same instances
--   - encoding: no order of evaluation is named across incomparable vertices → boxes are applied in lexicographic order; reason: lexicographic order extends the order along every qubit, and boxes sharing no qubit commute (proved in the verification file), so any other extension gives the same number
--   - encoding: a generalized preparation is a choice in V − R₁ → a total label s, whose values on O are ignored through glue; reason: the convention of the published HardyCausaloid.Region; same preparations
--   - encoding: the probability is the trace of the state after all the boxes → the real part of that trace (latticeProb); reason: the trace is real on the positive semidefinite matrices the boxes produce; same values
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, eq. (27) and steps 1–3 of the clumping method, p.14; §4.2, eq. (11), p.9; §4.3, eq. (13), p.10

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

/-- **The clumping method computes every probability of every region**, Hardy, arXiv:0804.0054v1,
§5, eq. (27) and steps 1–3 of the clumping method, p.14 ("The clumping method allows us to calculate
the Λ matrix for an arbitrary region R₁"), with eqs. (11) and (13), pp.9–10.

Let `M` be the model of the lattice with density matrix `ρ`, `S` a fiducial family, `L` fiducial
labels, and `C` the causaloid of the lattice. For every finite set `O` of vertices, every label `α`
of `R_O` and every generalized preparation `s`,
`p_α = r_α(R_O) · p(R_O)`, where `r_α(R_O)` is computed from `C` alone. -/
theorem clumping_computes_probabilities {m n : ℕ} (ρ : GlobalMat m n) (hρ : IsDensity ρ)
    (M : Model (Setting m n) (Outcome m n)) (hM : IsLatticeModel ρ M) (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) (hL : IsFiducialLabels S L)
    (O : Finset (X m n)) (α : Lab (Setting m n) (Outcome m n) O)
    (s : ∀ x, Label (Setting m n) (Outcome m n) x) :
    regionTable M O α s = (actualCausaloid S L).r O α ⬝ᵥ (actualCausaloid S L).state M O s := by sorry

end HardyFLocal
