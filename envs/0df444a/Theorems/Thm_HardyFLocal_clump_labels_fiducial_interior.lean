-- Prove2me | Theorems.Thm_HardyFLocal_clump_labels_fiducial_interior
-- name    : HardyFLocal.clump_labels_fiducial_interior
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:08.379408+00:00
-- url     : https://prove2.me/theorems/3140ff5c-7275-4393-9aae-a9cd5d750ed8
-- title:
--   §4.2, p.9 and §5, p.14 (corrected: for interior regions) — the clump labels are fiducial
-- statement:
--   Let $\rho$, $M$, $\$_k$, $L$ and the causaloid $C$ be as in the mission's goal. For every finite set $O$ of vertices with no vertex at the first or the last position of any qubit,
--
--   1. the state vectors $\mathbf p(R_O)$, over all generalized preparations, span $\mathbb R^{\Omega_C(O)}$;
--   2. the clump labels $\Omega_C(O)$ are a fiducial set of $R_O$: they suffice for every probability and no proper subset does.
--
--   This is the second level of compression: the labels of a region number sixteen per clump rather than 256 per vertex, and none can be spared.
--
--   For regions reaching the ends of the qubits this is false, which is the content of the correction below.
--
--   Differences from the source:
--   - correction: the clumping method and the two-step test apply to "an arbitrary region" and "an arbitrary probability" (p.14), with fiducial sets minimal (p.9) and (18) an if and only if (p.11) → minimality and the "only if" of (18) are stated for Interior regions, with no vertex at either end of a qubit; computing probabilities and the "if" direction stay at every region; reason: false as printed: on a 1 x 1 lattice with O1 empty, O2 the whole lattice and a sigma_z measurement of the right mover, every assumption of the source holds and the probability is well defined (one preparation), yet a is not a multiple of b; proved in the verification file
--   - reading: "a large number" of qubits → every m, n in ℕ, including small ones; reason: the statement is uniform in the lattice size and states nothing different on small lattices
--   - encoding: the labelling sentence of p.12 has v running from right to left → on a right mover (u, v) is followed by (u, v+1), on a left mover (u, v) by (u+1, v); reason: the explicit statement of p.13; it differs only by reversing both labellings
--   - reading: superoperators are "trace non-increasing maps on density operators that take allowed states to allowed states" → completely positive (finite Kraus form) and trace non-increasing; reason: the standard meaning; positivity alone fails on entangled inputs, which this lattice produces
--   - reading: "a general measurement" with a display panel, with no outcome count → an instrument with branches indexed by ℕ, zero branches allowed, HasSum normalization; reason: covers every finite instrument; the stronger reading, which adds the summability clause
--   - reading: the paper names no initial state → every density matrix on all the qubits, fixed once for the model; reason: entangled or not; the claim is uniform in it
--   - reading: a "fiducial spanning set of superoperators", with Λ in "a real vector space" (p.9) → a basis over ℝ of the Hermiticity-preserving one-qubit maps; reason: real coefficients are what p.9 requires, and they exist for Hermiticity-preserving maps
--   - reading: (21)–(22) take k′, k″ in {1} and k in Ω² → the earliest vertex of a clump carries the free label, later vertices the label 1, on each of the two qubits of a vertex; reason: this is the index placement of (21)–(22) applied to every clump
--   - encoding: the fiducial set has the smallest |Ω₁| (p.9) → the published HardyCausaloid.Fiducial, sufficient and inclusion-minimal; reason: for a linear span both mean a basis of the span of the rows of the table
--   - encoding: labels run from 1, and the first element of Ω² is 1 → labels are 0-based, and the first element of Ω² = Fin 16 is 0; reason: Lean convention; same instances
--   - encoding: no order of evaluation is named across incomparable vertices → boxes are applied in lexicographic order; reason: lexicographic order extends the order along every qubit, and boxes sharing no qubit commute (proved in the verification file), so any other extension gives the same number
--   - encoding: a generalized preparation is a choice in V − R₁ → a total label s, whose values on O are ignored through glue; reason: the convention of the published HardyCausaloid.Region; same preparations
--   - encoding: the probability is the trace of the state after all the boxes → the real part of that trace (latticeProb); reason: the trace is real on the positive semidefinite matrices the boxes produce; same values
--   - reading: "every probability in p is necessary in the specification of the state" (p.9) → in addition to Fiducial, the state vectors p(R_O) over all preparations span ℝ^{ΩC O}; reason: the parenthesis of p.9 says the fiducial probabilities are linearly independent functions of the preparation; the span statement is that, and it implies minimality
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §4.2, eqs. (10)–(11), p.9; §5, eqs. (21)–(22), p.13; clumping method, p.14

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

/-- **The clump labels are a fiducial set in the interior (corrected: for regions away from the ends
of the qubits)**, Hardy, arXiv:0804.0054v1, §4.2, eqs. (10)–(11), p.9 ("We chose the fiducial set Ω₁
of labels such that there is no other choice with smaller |Ω₁|"), with §5, eqs. (21)–(22), p.13, and
the clumping method, p.14.

For every region `O` with no vertex on the first or the last position of any qubit, the state
vectors `p(R_O)` on the clump labels span the whole of `ℝ^{ΩC O}`, and the clump labels are a fiducial
set of `R_O`.

**Formalization Note** The paper claims this for an arbitrary region. That fails at the ends of a
qubit: with `O₂` the whole lattice there is a single preparation, so the minimal fiducial set has
one element against `16^(m+n)` clump labels. -/
theorem clump_labels_fiducial_interior {m n : ℕ} (ρ : GlobalMat m n) (hρ : IsDensity ρ)
    (M : Model (Setting m n) (Outcome m n)) (hM : IsLatticeModel ρ M) (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x) (hL : IsFiducialLabels S L)
    (O : Finset (X m n)) (hO : Interior O) :
    Submodule.span ℝ
        (Set.range fun s : (∀ x, Label (Setting m n) (Outcome m n) x) =>
          (actualCausaloid S L).state M O s) = ⊤ ∧
    Fiducial (regionTable M O) ((actualCausaloid S L).fidSet O) := by sorry

end HardyFLocal
