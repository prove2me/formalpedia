-- Prove2me | Theorems.Thm_InvariantMoneySecurity_Decomposition_acceptance_vs_accepted_weight
-- name    : InvariantMoneySecurity.Decomposition.acceptance_vs_accepted_weight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:00:47.765194+00:00
-- url     : https://prove2.me/theorems/83db7073-553d-4c43-a51a-7ae59b8c6d49
-- title:
--   Lemma 3.4 — acceptance probability versus accepted weight
-- statement:
--   Let $\rho$ be any positive semidefinite trace-one state, $p$ any serial number, $r\ge1$ any verifier round count, and $\Delta$ the minimum orbit gap of the finite inverse-closed move system. Then
--   $$\operatorname{aw}_p(\rho)\le\operatorname{Acc}_p(\rho)\le\operatorname{aw}_p(\rho)+\bigl(1-\operatorname{aw}_p(\rho)\bigr)(1-\Delta)^{2r}.$$
--   Both bounds hold for mixed states, all same-serial orbits, and arbitrary round counts, without rapid mixing. The exact multiplicative factor and exponent are preserved. This compares the concrete finite-round verifier with its fixed-space projector. In the padded physical register, invalid-encoding weight rejects; the same inequalities hold even for states containing such weight.
--
--   Differences from the source:
--   - generalization: finite data of an efficient invariant money family at n ≥ 1 → any finite nonempty inverse-closed distinct move system, including n = 0; reason: the spectral conclusions use only the finite permutation system; every source instance specializes to these data
--   - generalization: density states on the logical object register → all density states on the padded qubit register, including invalid-encoding weight; reason: the walk and accepted projector vanish on invalid encodings; their rejecting weight only increases the available upper-bound remainder
--   - generalization: serial numbers, the values of I → every bit string of the serial width, including strings outside the image of I; reason: the level set and both projectors are then zero, so equation (8) reads 0 ≤ 0 ≤ (1 − Δ)^{2r}
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), p. 11, Lemma 3.4, equation (8)

import Definitions.Def_InvariantMoneySecurity_Decomposition_MintVerifier
set_option autoImplicit false
open scoped ComplexOrder

namespace InvariantMoneySecurity.Decomposition

/-- Lemma 3.4, p. 11, equation (8), with the exact factor and exponent.
The padded invalid-object subspace rejects, so arbitrary physical density matrices are allowed. -/
theorem acceptance_vs_accepted_weight {n : ℕ} (D : FiniteScheme n)
    (p : Bits D.serialBits) (r : ℕ) (hr : 1 ≤ r)
    (ρ : Matrix (Bits n) (Bits n) ℂ) (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    D.acceptedWeight p ρ ≤ D.acceptance p r ρ ∧
    D.acceptance p r ρ ≤ D.acceptedWeight p ρ +
      (1 - D.acceptedWeight p ρ) * (1 - D.gap) ^ (2 * r) := by sorry

end InvariantMoneySecurity.Decomposition
