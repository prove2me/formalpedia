-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_of_one_comp_eq_one_comp_of_forall_comp_eq_comp_of_isAlgClosed
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.eq_of_one_comp_eq_one_comp_of_forall_comp_eq_comp_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/88269375-8c98-538c-a63d-a9376814bc6f
-- title:
--   Rigidity: endomorphisms agreeing on unit and geometric points
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism satisfying `AbelianSchemePropertyBundle`, that is: $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} R$ the fibre $f^{-1}(s)$ (preimage under the underlying map of spaces) is connected and nonempty, and $f$ admits at least one relative group law. Let $L$ be such a relative group law: for every scheme $T$ and every $t : T \to \operatorname{Spec} R$ a multiplication, unit and inversion on the set of $T$-points $\{\varphi : T \to A \mid \varphi \circ f = t\}$, satisfying associativity, the two unit laws and left inverse cancellation, and with the multiplication compatible with precomposition by any $\chi : T' \to T$ with $t \circ \chi = t'$. Let $\varphi, \psi : A \to A$ be morphisms over $\operatorname{Spec} R$, i.e. $f \circ \varphi = f = f \circ \psi$. Assume $\varphi$ and $\psi$ agree after precomposition with the unit section $L.one(\mathrm{id}_{\operatorname{Spec} R}) : \operatorname{Spec} R \to A$, and that for every algebraically closed field $k$ (in the same universe) and every morphism $x : \operatorname{Spec} k \to A$ one has $\varphi \circ x = \psi \circ x$; no compatibility of $x$ with $f$ is required. Then $\varphi = \psi$.
--
--   This is the two-morphism form of the rigidity lemma for abelian schemes over an arbitrary affine base, possibly non-reduced and with disconnected spectrum: a morphism of $A$ over $\operatorname{Spec} R$ is determined by its effect on the unit section and on all geometric points. Neither $\varphi$ nor $\psi$ is assumed to respect the group law, and $L$ is not assumed commutative; the result is used in the treatment of polarised abelian schemes and in further rigidity statements for Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_of_one_comp_eq_one_comp_of_forall_comp_eq_comp_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.eq_of_one_comp_eq_one_comp_of_forall_comp_eq_comp_of_isAlgClosed
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (L : RelativeGroupLaw R f)
    (φ ψ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ φ = (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ ψ)
    (hfix : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ A), x ≫ φ = x ≫ ψ) :
    φ = ψ := by sorry
