-- Prove2me | Theorems.Thm_HardyFLocal_clumping_respects_f_locality
-- name    : HardyFLocal.clumping_respects_f_locality
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:04.394836+00:00
-- url     : https://prove2.me/theorems/90d75cd3-41c9-42cf-a43c-dd857c57ad78
-- title:
--   §5, p.14 — the clumping method respects F-locality
-- statement:
--   Let $L$ be labels at the vertices of the lattice, $O$ a finite set of vertices, and $(T,E)$, $(T',E')$ pairs of tables with $T_{xx'}=T'_{xx'}$ on every sequential pair of vertices $x,x'\in O$ and $E_x=E'_x$ for every $x\in O$. Then the two clumped causaloids have the same
--   $$\Omega_C(O),\qquad \Lambda(O),\qquad \mathbf r_\alpha(R_O)\ \text{ for every label }\alpha\text{ of }R_O.$$
--
--   So predictions for a region use only objects pertaining to that region, which is the property the paper is named for.
--
--   Differences from the source:
--   - reading: "we only use Λ matrices pertaining to regions R̃₁ ⊆ R₁" → for tables T, E as arguments: tables agreeing on the sequential pairs inside O and the vertices of O give the same ΩC O, Λ O and r_α; reason: the informal remark, as a statement about which entries of the tables are read
--   - reading: "a large number" of qubits → every m, n in ℕ, including small ones; reason: the statement is uniform in the lattice size and states nothing different on small lattices
--   - encoding: the labelling sentence of p.12 has v running from right to left → on a right mover (u, v) is followed by (u, v+1), on a left mover (u, v) by (u+1, v); reason: the explicit statement of p.13; it differs only by reversing both labellings
--   - reading: (21)–(22) take k′, k″ in {1} and k in Ω² → the earliest vertex of a clump carries the free label, later vertices the label 1, on each of the two qubits of a vertex; reason: this is the index placement of (21)–(22) applied to every clump
--   - encoding: labels run from 1, and the first element of Ω² is 1 → labels are 0-based, and the first element of Ω² = Fin 16 is 0; reason: Lean convention; same instances
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, p.14

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

/-- **The clumping method respects F-locality**, Hardy, arXiv:0804.0054v1, §5, p.14 ("We note that the
clumping method respects F-locality since, in calculating the Λ matrix for R₁, we only use Λ matrices
pertaining to regions R̃₁ ⊆ R₁").

Let `(T, E)` and `(T', E')` be tables that agree on the sequential pairs of vertices inside `O` and
on the vertices of `O`. Then the two clumped causaloids have the same fiducial set `ΩC O`, the same
matrix `Λ O`, and the same vector `r_α(R_O)` for every label `α` of `R_O`. -/
theorem clumping_respects_f_locality {m n : ℕ}
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)
    (T T' : X m n → X m n → PairTable)
    (E E' : ∀ x : X m n, Label (Setting m n) (Outcome m n) x → Ω × Ω → ℝ)
    (O : Finset (X m n))
    (hT : ∀ x ∈ O, ∀ x' ∈ O, IsSequentialPair x x' → T x x' = T' x x')
    (hE : ∀ x ∈ O, E x = E' x) :
    (clumpCausaloid L T E).ΩC O = (clumpCausaloid L T' E').ΩC O ∧
    (∀ (l : ∀ x : O, omegaOne L x.1) (k : omegaC L O),
      (clumpCausaloid L T E).Λ O l k = (clumpCausaloid L T' E').Λ O l k) ∧
    ∀ α : Lab (Setting m n) (Outcome m n) O,
      (clumpCausaloid L T E).r O α = (clumpCausaloid L T' E').r O α := by sorry

end HardyFLocal
