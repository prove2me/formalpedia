-- Prove2me | Theorems.Thm_HardyFLocal_symmetry_determines_causaloid
-- name    : HardyFLocal.symmetry_determines_causaloid
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:41:36.274619+00:00
-- url     : https://prove2.me/theorems/f1a5ae01-6472-4fab-a60e-0bc3c98a4402
-- title:
--   Eqs. (27)–(28), p.14 — the symmetry property
-- statement:
--   Let $\$_k$ be a fiducial family, and let $E$, $T$ be tables such that for every vertex $x$ and label $\alpha$,
--   $$\$_\alpha=\sum_{a,b}E_x(\alpha)^{ab}\,\$_a\otimes\$_b,$$
--   and for every sequential pair $x,x'$, on right or on left movers, and all $l',l$,
--   $$\$_{l'}\circ\$_l=\sum_k T_{xx'}{}^{\,k}_{l'l}\,\$_k.$$
--   Then:
--
--   1. $E_x(\alpha)$ is the elementary table of $\$_\alpha$, so it does not depend on the vertex, and depends on the label only through its superoperator;
--   2. $T_{xx'}$ is the pair table at every sequential pair;
--   3. on every region, the clumped causaloid of $(T,E)$ has the same $\Lambda$ and $\mathbf r_\alpha$ as the causaloid of the lattice.
--
--   So the two tables of (28) determine the whole list (27). This is the paper's third level of compression.
--
--   Differences from the source:
--   - reading: "the Λ matrices of each type are the same. Hence, we can actually specify the causaloid by" (28) → tables solving (20) at every vertex and (21) at every sequential pair equal one elementary and one pair table, and give the same Λ and r on every region; reason: the prose claim, stated for tables solving the equations the page cites
--   - reading: "a large number" of qubits → every m, n in ℕ, including small ones; reason: the statement is uniform in the lattice size and states nothing different on small lattices
--   - encoding: the labelling sentence of p.12 has v running from right to left → on a right mover (u, v) is followed by (u, v+1), on a left mover (u, v) by (u+1, v); reason: the explicit statement of p.13; it differs only by reversing both labellings
--   - reading: a "fiducial spanning set of superoperators", with Λ in "a real vector space" (p.9) → a basis over ℝ of the Hermiticity-preserving one-qubit maps; reason: real coefficients are what p.9 requires, and they exist for Hermiticity-preserving maps
--   - reading: (21)–(22) take k′, k″ in {1} and k in Ω² → the earliest vertex of a clump carries the free label, later vertices the label 1, on each of the two qubits of a vertex; reason: this is the index placement of (21)–(22) applied to every clump
--   - encoding: labels run from 1, and the first element of Ω² is 1 → labels are 0-based, and the first element of Ω² = Fin 16 is 0; reason: Lean convention; same instances
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, eqs. (27)–(28), p.14

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

/-- **The symmetry property: (28) determines (27)**, Hardy, arXiv:0804.0054v1, §5, eqs. (27)–(28), p.14
("Second, we note the symmetry property that, according to (20) and (21), the Λ matrices of each type
are the same. Hence, we can actually specify the causaloid by …").

Let `E` solve (20) at every vertex and `T` solve (21) at every sequential pair, on right and on left
movers. Then `E` is the one table `elemCoeff S`, depending on a label only through its superoperator
and not on the vertex; `T` is the one table `pairTable S` at every sequential pair; and so the
clumped causaloid of `(T, E)` has, on every region, the same `Λ` and `r` as the causaloid of the
lattice, which is computed from these two tables. -/
theorem symmetry_determines_causaloid {m n : ℕ} (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)
    (T : X m n → X m n → PairTable)
    (E : ∀ x : X m n, Label (Setting m n) (Outcome m n) x → Ω × Ω → ℝ)
    (hE : ∀ x α, labelOp α = ∑ p : Ω × Ω, E x α p • prodOp (S.map p.1) (S.map p.2))
    (hT : ∀ x x', IsSequentialPair x x' → ∀ l' l,
      S.map l' ∘ₗ S.map l = ∑ k, T x x' l' l k • S.map k) :
    (∀ x α, E x α = elemCoeff S (labelOp α)) ∧
    (∀ x x', IsSequentialPair x x' → T x x' = pairTable S) ∧
    (∀ (x x' : X m n) (α : Label (Setting m n) (Outcome m n) x)
        (α' : Label (Setting m n) (Outcome m n) x'),
      labelOp α = labelOp α' → E x α = E x' α') ∧
    ∀ O : Finset (X m n),
      (∀ (l : ∀ x : O, omegaOne L x.1) (k : omegaC L O),
        (clumpCausaloid L T E).Λ O l k = (actualCausaloid S L).Λ O l k) ∧
      ∀ α : Lab (Setting m n) (Outcome m n) O,
        (clumpCausaloid L T E).r O α = (actualCausaloid S L).r O α := by sorry

end HardyFLocal
