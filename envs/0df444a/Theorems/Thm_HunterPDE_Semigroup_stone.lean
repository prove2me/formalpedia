-- Prove2me | Theorems.Thm_HunterPDE_Semigroup_stone
-- name    : HunterPDE.Semigroup.stone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:09:35.193844+00:00
-- url     : https://prove2.me/theorems/96f8f280-5cdd-4652-8245-babc441dfab6
-- title:
--   Theorem 5.42 — Stone's theorem: iA generates a C₀ unitary group iff A is self-adjoint
-- statement:
--   Let $\mathcal{H}$ be a complex Hilbert space and $A : \mathcal{D}(A) \subset \mathcal{H} \to \mathcal{H}$ a linear operator; let $iA$ be the operator $f \mapsto i\,Af$ with the same domain $\mathcal{D}(iA) = \mathcal{D}(A)$. Then
--   $$iA \text{ is the generator of a strongly continuous unitary group on } \mathcal{H} \iff A \text{ is self-adjoint.}$$
--
--   Stone's theorem identifies unitary dynamics, such as the Schrödinger group $e^{it\Delta}$, with self-adjoint generators.
--
--   **Formalization Note.** Self-adjointness is Definition 5.41 as stated in the notes (dense domain, $\mathcal{D}(A) = \mathcal{D}(A^*)$, symmetry). The generator of the group $\{T(t) : t \in \mathbb{R}\}$ is taken in the sense of Definition 5.30, i.e. as the generator of its forward part $\{T(t) : t \ge 0\}$, since the notes define generators only for semigroups; for a C₀ group this coincides with the two-sided definition.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 149, Theorem 5.42

import Mathlib
import Definitions.Def_HunterPDE_Semigroup_C0Semigroup
import Definitions.Def_HunterPDE_Semigroup_SelfAdjoint

namespace HunterPDE.Semigroup

/-- Theorem 5.42 (Stone) of Hunter, *Notes on PDEs* (p. 149). An operator
`iA : D(iA) ⊂ H → H` in a complex Hilbert space `H` is the generator of a strongly continuous
unitary group on `H` if and only if `A` is self-adjoint (Definition 5.41).

`iA` is `Complex.I • A`, with domain `D(iA) = D(A)`. The generator of the group `{T(t)}` is that
of Definition 5.30, i.e. of its forward part `{T(t) : t ≥ 0}` (the notes define generators only
for semigroups; §5.4.3 identifies a C₀ group with a C₀ semigroup of invertible operators with
`T(−t) = T(t)⁻¹`). -/
theorem stone {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →ₗ.[ℂ] H) :
    (∃ T : ℝ → H →L[ℂ] H, IsUnitaryGroup T ∧ IsGenerator T (Complex.I • A)) ↔
      IsSelfAdjointOp A := by sorry

end HunterPDE.Semigroup
