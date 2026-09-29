-- Prove2me | Theorems.Thm_IsLocalRing_exists_isDiscreteValuationRing_moduleFinite_algHom_injective_comp_eq_of_moduleFinite
-- name    : IsLocalRing.exists_isDiscreteValuationRing_moduleFinite_algHom_injective_comp_eq_of_moduleFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/b53693b0-a85a-58bb-879e-4e768cdda1f2
-- title:
--   Descent of a field-valued point to a finite complete DVR
-- statement:
--   Let $\mathcal O$ be a commutative ring which is a domain and a discrete valuation ring, complete with respect to the adic topology of its maximal ideal, with finite residue field and of characteristic zero. Let $A$ be a commutative $\mathcal O$-algebra that is finite as an $\mathcal O$-module, let $L$ be a field carrying an $\mathcal O$-algebra structure whose structure map $\mathcal O \to L$ is injective, and let $\chi : A \to L$ be a homomorphism of $\mathcal O$-algebras. The assertion is that there exists a type $\mathcal O'$ together with a commutative ring structure making it a domain and a discrete valuation ring, complete for the adic topology of its maximal ideal, with finite residue field and of characteristic zero, together with an $\mathcal O$-algebra structure on $\mathcal O'$ for which $\mathcal O'$ is finite as an $\mathcal O$-module and the structure map $\mathcal O \to \mathcal O'$ is a local homomorphism, and there exist $\mathcal O$-algebra homomorphisms $j : \mathcal O' \to L$ and $\psi : A \to \mathcal O'$ such that $j$ is injective and $j(\psi(a)) = \chi(a)$ for every $a \in A$; that is, $\chi$ factors as $\psi$ followed by the embedding $j$.
--
--   This is the standard descent of a point of a module-finite algebra with values in an arbitrary field (for instance a geometric point, or a point with values in a large $p$-adic field) to a point with values in a finite extension of the coefficient ring. It is used in the local study of Hecke algebras attached to cusp forms, where a character of a Hecke algebra valued in an algebraically closed field must be realised over a finite complete discrete valuation ring of coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_isDiscreteValuationRing_moduleFinite_algHom_injective_comp_eq_of_moduleFinite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_isDiscreteValuationRing_moduleFinite_algHom_injective_comp_eq_of_moduleFinite
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]
    (L : Type) [Field L] [Algebra 𝒪 L] (hL : Function.Injective (algebraMap 𝒪 L))
    (χ : A →ₐ[𝒪] L) :
    ∃ (𝒪' : Type) (_ : CommRing 𝒪') (_ : IsDomain 𝒪') (_ : IsDiscreteValuationRing 𝒪')
      (_ : IsAdicComplete (maximalIdeal 𝒪') 𝒪') (_ : Finite (ResidueField 𝒪')) (_ : CharZero 𝒪')
      (_ : Algebra 𝒪 𝒪') (_ : Module.Finite 𝒪 𝒪') (_ : IsLocalHom (algebraMap 𝒪 𝒪'))
      (j : 𝒪' →ₐ[𝒪] L) (ψ : A →ₐ[𝒪] 𝒪'),
      Function.Injective j ∧ ∀ a : A, j (ψ a) = χ a := by sorry
