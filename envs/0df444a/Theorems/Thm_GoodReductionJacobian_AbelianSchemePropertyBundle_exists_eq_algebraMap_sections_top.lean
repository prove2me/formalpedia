-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_algebraMap_sections_top
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_algebraMap_sections_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/2234f263-ef9f-5316-b2af-110a8499a942
-- title:
--   Global sections of an abelian scheme over a field are constants
-- statement:
--   Let $K$ be a field and let $f : A \to \operatorname{Spec} K$ be a morphism of schemes (all in a single universe) satisfying the property bundle `AbelianSchemePropertyBundle`, i.e. $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} K$ the fibre $f^{-1}(\{s\})$ (preimage of the singleton under the underlying continuous map) is connected, and the set of relative group laws on $f$ — systems of functorial multiplication, unit and inversion operations on $T$-points over $\operatorname{Spec} K$, subject to associativity, the unit laws, left inverses and compatibility with base change along morphisms over $\operatorname{Spec} K$ — is nonempty. Let $\mathcal{K}$ be an ordered affine cover of $A$: a finite linearly ordered index type together with opens $U_i \subseteq A$, each affine, whose supremum is $\top$. Let $s \in \Gamma(A, \top)$ be a global section of the structure sheaf. Equip $\Gamma(A,\top)$ with the $K$-algebra structure coming from $f$, namely the ring map obtained from the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} K) \cong K$ followed by $f$ on sections over $\top$. Then there is a scalar $c \in K$ with $s = \mathrm{algebraMap}\,K\,\Gamma(A,\top)\,(c)$.
--
--   This is the standard statement that an abelian variety over a field has only constant global regular functions, $\Gamma(A,\mathcal{O}_A) = K$, in the form needed here for a smooth proper morphism with connected fibres carrying a relative group law. It is used in the Čech-theoretic construction of invariant differentials and primitive elements over such a scheme, and in the uniqueness part of the statement that a scalar is determined by the associated Riemann form datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_algebraMap_sections_top.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_algebraMap_sections_top
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (𝒦 : A.OrderedAffineCover) (s : Γ(A, ⊤)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
    ∃ c : K, s = algebraMap K Γ(A, ⊤) c := by sorry
