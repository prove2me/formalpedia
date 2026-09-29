-- Prove2me | Theorems.Thm_NumberField_InfPlaceDecomp_localBridge_hypotheses_archimedean
-- name    : NumberField.InfPlaceDecomp.localBridge_hypotheses_archimedean
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/58eb3805-2299-5394-9072-71fd140b2e08
-- title:
--   Archimedean local-bridge hypotheses: level, divisibility, degree-one acyclicity
-- statement:
--   Let $F$ be an intermediate field of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is a number field, Galois over $\mathbb{Q}$ and totally complex, let $w$ be an infinite place of $F$, and let $\sigma$ be a $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$. Write $\langle c\rangle$ for `archimedeanDecomposition`, the subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of integral powers of [`complexConjugation`](def/GaloisRep_ComplexConjugation.html#L30) (the restriction to $\overline{\mathbb{Q}}$ of complex conjugation on $\mathbb{C}$), and $D_w$ for `decomp ℚ F w`, the stabiliser of $w$ in $\mathrm{Gal}(F/\mathbb{Q})$ for the action on infinite places. Assume given a group homomorphism $\pi_i \colon \langle c\rangle \to D_w$ such that for every $h \in \langle c\rangle$ the element $\pi_i(h)$ of $\mathrm{Gal}(F/\mathbb{Q})$ is the restriction to $F$ of $\sigma^{-1} h \sigma$, that $\pi_i$ is bijective, and that $\sigma^{-1} c \sigma$ does not lie in the fixing subgroup of $F$ in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$. Then three assertions hold. First, the only $s \in \langle c\rangle$ whose underlying automorphism of $\overline{\mathbb{Q}}$ (the image under `archimedeanLoc`, the inclusion of the subgroup) fixes $F$ pointwise is $s = 1$. Second, for all additive commutative groups $V$ and $W$ with $W$ free and finite over $\mathbb{Z}$, every injective $\mathbb{Z}$-linear $f \colon V \to W$ and every $\mathbb{Z}$-linear $\varphi \colon V \to \mathrm{Additive}\,(F_w)^{\times}$, where $F_w$ is the completion of $F$ at $w$, there is a $\mathbb{Z}$-linear $\psi \colon W \to \mathrm{Additive}\,(F_w)^{\times}$ with $\psi(f(v)) = \varphi(v)$ for all $v \in V$; that is, the unit group of the completion, written additively, is injective relative to such extensions. Third, for every finite type $\alpha$, every $1$-cocycle $u$ of the $\langle c\rangle$-representation obtained as the internal hom (`ihom`) from the free $\mathbb{Z}$-representation `Rep.free ℤ (F ≃ₐ[ℚ] F) α` of $\mathrm{Gal}(F/\mathbb{Q})$, restricted along the inclusion $D_w \hookrightarrow \mathrm{Gal}(F/\mathbb{Q})$ and then along $\pi_i$, into the restriction along $\pi_i$ of `localUnits ℚ F w` (the $D_w$-module $(F_w)^{\times}$ with its multiplicative action), is a coboundary: there is an element $\chi$ of that hom-representation with $d_{01}\chi = u$ as a function on $\langle c\rangle$.
--
--   These are the arithmetic inputs required of an infinite place in the local-bridge construction — triviality of the level subgroup, divisibility of the local unit group, and vanishing of degree-one cohomology for the relevant hom-module — forming the archimedean counterpart of the corresponding statement at a finite place. It is cited by [`NumberField.InfPlaceDecomp.exists_isLocalBridge1_archimedean`](thm.html#NumberField.InfPlaceDecomp.exists_isLocalBridge1_archimedean), [`NumberField.InfPlaceDecomp.exists_isLocalBridge2_archimedean`](thm.html#NumberField.InfPlaceDecomp.exists_isLocalBridge2_archimedean) and [`groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two`](thm.html#groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfPlaceDecomp_localBridge_hypotheses_archimedean.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem NumberField.InfPlaceDecomp.localBridge_hypotheses_archimedean
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [IsTotallyComplex ↥F]
    (w : InfinitePlace ↥F)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (πi : ↥archimedeanDecomposition →* ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ h : ↥archimedeanDecomposition,
      ((πi h : ↥(NumberField.InfPlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
        AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * σ))
    (hπbij : Function.Bijective πi)
    (hσF : σ⁻¹ * complexConjugation * σ ∉ F.fixingSubgroup) :

    (∀ s : ↥archimedeanDecomposition, archimedeanLoc s ∈ F.fixingSubgroup → s = 1) ∧

    (∀ (V W : Type) [AddCommGroup V] [AddCommGroup W] [Module.Free ℤ W] [Module.Finite ℤ W]
        (f : V →ₗ[ℤ] W) (_ : Function.Injective f) (φ : V →ₗ[ℤ] Additive (w.Completion)ˣ),
      ∃ ψ : W →ₗ[ℤ] Additive (w.Completion)ˣ, ∀ v : V, ψ (f v) = φ v) ∧

    (∀ (α : Type) [Finite α]
        (u : groupCohomology.cocycles₁ ((ihom (Rep.res πi (Rep.res (NumberField.InfPlaceDecomp.decomp ℚ ↥F w).subtype
          (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) α)))).obj (Rep.res πi (NumberField.InfPlaceDecomp.localUnits ℚ ↥F w)))),
      ∃ χ : (ihom (Rep.res πi (Rep.res (NumberField.InfPlaceDecomp.decomp ℚ ↥F w).subtype (Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) α)))).obj
          (Rep.res πi (NumberField.InfPlaceDecomp.localUnits ℚ ↥F w)),
        (groupCohomology.d₀₁ _).hom χ = (u : ↥archimedeanDecomposition → _)) := by sorry
