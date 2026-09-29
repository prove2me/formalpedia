-- Prove2me | Theorems.Thm_LanglandsTunnell_det_lift_eq_chiNegThree_of_isFrobeniusAt
-- name    : LanglandsTunnell.det_lift_eq_chiNegThree_of_isFrobeniusAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/5a7fe2f8-8ef9-5ba6-9cae-82383aa70ac4
-- title:
--   Determinant of the explicit lift equals χ₋₃ at Frobenius
-- statement:
--   Let $\rho$ be a group homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) = \mathrm{AlgebraicClosure}\,\mathbb Q \simeq_{\mathbb Q} \mathrm{AlgebraicClosure}\,\mathbb Q$ to $\mathrm{GL}_2(\mathbb Z/3)$ such that for every $\sigma$ the determinant $\det \rho(\sigma) \in (\mathbb Z/3)^\times$ equals $\mathrm{modThreeCyclotomicChar}(\sigma)$, the character obtained from Mathlib's `modularCyclotomicCharacter` of $\overline{\mathbb Q}$ at $3$. Let $\Psi$ be a group homomorphism $\mathrm{GL}_2(\mathbb Z/3) \to \mathrm{GL}_2(\mathbb Z[\sqrt{-2}])$ which is a section of entrywise reduction along `red`, the ring homomorphism $\mathbb Z[\sqrt{-2}] \to \mathbb Z/3$ sending $\sqrt{-2} \mapsto -1$: that is, $\mathrm{GL}_2(\mathrm{red})(\Psi(g)) = g$ for all $g$. Let $p$ be a prime with $p \neq 3$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, and let $\sigma$ be an automorphism lying in the decomposition subgroup of $A$ over $\mathbb Q$ and acting on the residue field of $A$ by $x \mapsto x^p$. Then the determinant of the matrix underlying $\Psi(\rho(\sigma))$ equals the image in $\mathbb Z[\sqrt{-2}]$ of the integer $\mathrm{chiNegThree}(p)$, which is $1$ if $p \equiv 1 \pmod 3$, $-1$ if $p \equiv 2 \pmod 3$, and $0$ otherwise.
--
--   This is the determinant clause in the passage from a mod-$3$ representation with cyclotomic determinant to the weight-one setting of the Langlands–Tunnell theorem: the lifted representation $\Psi \circ \rho$ has determinant the odd quadratic character $\chi_{-3}$ of conductor $3$, which becomes the nebentypus of the associated weight-one form. It is used in the construction of the weight-one object realising $\chi_{-3}$ together with the trace of the lift, in [`LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift_cuspForm`](thm.html#LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift_cuspForm) and in the companion existence statement under the inertia and coprimality conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_det_lift_eq_chiNegThree_of_isFrobeniusAt.lean

import Mathlib
import Definitions.Def_GaloisRep_ModThreeCyclotomic
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve FLT.ExplicitLift EisensteinWeightOne
open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem LanglandsTunnell.det_lift_eq_chiNegThree_of_isFrobeniusAt
    (ρ : Γℚ →* GL (Fin 2) (ZMod 3))
    (hdet : ∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g)
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : Γℚ) (hσ : A.IsFrobeniusAt σ p) :
    ((Ψ (ρ σ) : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))).det =
      ((chiNegThree p : ℤ) : ℤ√(-2)) := by sorry
