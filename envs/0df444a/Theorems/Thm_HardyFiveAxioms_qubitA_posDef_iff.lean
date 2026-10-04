-- Prove2me | Theorems.Thm_HardyFiveAxioms_qubitA_posDef_iff
-- name    : HardyFiveAxioms.qubitA_posDef_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T23:50:00.598348+00:00
-- url     : https://prove2.me/theorems/1e2ccb7f-0040-4d0b-a421-6d0df8629ce0
-- title:
--   Qubit: $A$ is positive definite (ellipsoid) $\iff c_-<c<c_+$
-- statement:
--   Let $0\le a,b\le1$ and $c\in\mathbb R$, and let $A=A(a,b,c)$ be the matrix (83). Then $A$ has three positive eigenvalues, i.e. it is positive definite and the surface $\vec v^{\,T}A\vec v=\tfrac12$ is an ellipsoid, if and only if
--
--   $$c_-<c<c_+ .$$
--
--   This is Eq. (86). Hardy argues that pure states must lie on an ellipsoid, and this yields exactly the quantum constraint (36) on $c$.
--
--   **Formalization Note** "Three positive eigenvalues" is encoded as `Matrix.PosDef` (symmetric with $x^TAx>0$ for $x\neq0$), which is equivalent for real symmetric matrices.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, pp. 21–22, Section 8.6, Eqs. (83)–(86)

import Mathlib
import Definitions.Def_hardy2001_qubit

namespace HardyFiveAxioms

/-- Hardy 2001, Section 8.6, Eq. (86): for `0 ≤ a, b ≤ 1`, the matrix `A` has three positive
eigenvalues (the surface `v⃗ᵀ A v⃗ = 1/2` is an ellipsoid) if and only if `c₋ < c < c₊`. -/
theorem qubitA_posDef_iff (a b c : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1) :
    (qubitA a b c).PosDef ↔ cMinus a b < c ∧ c < cPlus a b := by sorry

end HardyFiveAxioms
