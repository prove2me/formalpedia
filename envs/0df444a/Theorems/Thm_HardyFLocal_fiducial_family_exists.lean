-- Prove2me | Theorems.Thm_HardyFLocal_fiducial_family_exists
-- name    : HardyFLocal.fiducial_family_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:29.852203+00:00
-- url     : https://prove2.me/theorems/d827edd8-a244-48d9-9fdc-223bfe05fbe0
-- title:
--   §5, p.13 — a fiducial family with $\$_1=I$ exists, and has labels
-- statement:
--   There is a fiducial family: sixteen completely positive, trace non-increasing one-qubit maps forming a real basis of the Hermiticity-preserving maps, with
--   $$\$_1=I.$$
--   Moreover, for each fiducial family and each lattice size $m,n$, there are labels $L_x(a,b)$ at every vertex with superoperator $\$_a\otimes\$_b$: each product of fiducial maps is an outcome of some instrument.
--
--   So the hypotheses on the fiducial data in the mission's goal can be met.
--
--   Differences from the source:
--   - reading: "a large number" of qubits → every m, n in ℕ, including small ones; reason: the statement is uniform in the lattice size and states nothing different on small lattices
--   - reading: superoperators are "trace non-increasing maps on density operators that take allowed states to allowed states" → completely positive (finite Kraus form) and trace non-increasing; reason: the standard meaning; positivity alone fails on entangled inputs, which this lattice produces
--   - reading: "a general measurement" with a display panel, with no outcome count → an instrument with branches indexed by ℕ, zero branches allowed, HasSum normalization; reason: covers every finite instrument; the stronger reading, which adds the summability clause
--   - reading: a "fiducial spanning set of superoperators", with Λ in "a real vector space" (p.9) → a basis over ℝ of the Hermiticity-preserving one-qubit maps; reason: real coefficients are what p.9 requires, and they exist for Hermiticity-preserving maps
--   - encoding: labels run from 1, and the first element of Ω² is 1 → labels are 0-based, and the first element of Ω² = Fin 16 is 0; reason: Lean convention; same instances
--   - reading: "we choose $₁ = I" (an act of choice, with the fiducial set and the boxes assumed available) → a fiducial family with first member the identity exists, and every fiducial family has labels at every vertex whose superoperators are the products $_a ⊗ $_b; reason: the choice the page makes is possible exactly when such a family and such labels exist; this is what makes the goal's hypotheses satisfiable
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, p.13

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

/-- **The choice `$₁ = I` can be made**, Hardy, arXiv:0804.0054v1, §5, p.13 ("For reasons that will
be clear later, we choose $₁ = I where 1 is the first element of Ω² and I is the identity
superoperator").

A fiducial family exists, with its first member the identity. For every fiducial family and every
lattice, there are labels at every vertex whose superoperators are the products `$_a ⊗ $_b`. -/
theorem fiducial_family_exists :
    Nonempty FiducialFamily ∧
    ∀ (S : FiducialFamily) (m n : ℕ),
      ∃ L : (∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x), IsFiducialLabels S L := by sorry

end HardyFLocal
