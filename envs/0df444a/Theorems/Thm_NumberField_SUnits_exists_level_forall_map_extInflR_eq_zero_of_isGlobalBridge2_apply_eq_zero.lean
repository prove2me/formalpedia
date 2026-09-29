-- Prove2me | Theorems.Thm_NumberField_SUnits_exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero
-- name    : NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/682d2d8a-d8e8-5d37-916f-8f783699e9cf
-- title:
--   Kernel of the global degree-two bridge dies under inflation
-- statement:
--   Fix a prime $p$, a finite set $S$ of primes containing $p$ (as `pPrime p`), and a finite set $S_{\mathbb Q}$ of height-one primes of $\mathcal O_{\mathbb Q}$ whose underlying set is $\{w : \exists q\in S,\ q\in w\}$. Let $M$ be a representation of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ over $\mathbb Z/p$, and let $F_1\subseteq\overline{\mathbb Q}$ be an intermediate field which is a number field, Galois over $\mathbb Q$, and satisfies `IsUnramifiedOutside S`: $F_1/\mathbb Q$ is finite and for every prime $q\notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$, the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ lies in the fixing subgroup of $F_1$; assume further that every element of that fixing subgroup acts trivially on $M$. Let $B$ be a $\mathbb Z[\mathrm{Gal}(F_1/\mathbb Q)]$-representation, finite as a type, with $pB=0$. Let $\iota_{E_1}$ be an additive map from the $S_{\mathbb Q}$-unit representation [`NumberField.SUnits.sUnitsRep ℚ F₁ Sℚ`](def/NumberField_SUnitsModule.html#L52) to $\mathrm{Additive}\,\overline{\mathbb Q}^{\times}$ induced by $F_1\hookrightarrow\overline{\mathbb Q}$ on units, and assume every $p$-th root of unity of $\overline{\mathbb Q}$ lies in its image. Let $\kappa\colon B\to(M\to\mathrm{Additive}\,\overline{\mathbb Q}^{\times})$ be biadditive, equivariant in the sense $\kappa(\rho_B(\gamma|_{F_1})b)(\rho_M(\gamma)m)=\gamma\cdot\kappa(b)(m)$ for the action `Rep.ofAlgebraAutOnUnits` on $\overline{\mathbb Q}^{\times}$, and perfect on the $M$ side: every additive $c\colon B\to\mathrm{Additive}\,\overline{\mathbb Q}^{\times}$ equals $\kappa(\cdot)(m)$ for a unique $m\in M$. Finally let $$\Lambda_1\colon H^1\bigl(\mathrm{Gal}(F_1/\mathbb Q),\mathrm{Hom}(\mathtt{relationModuleInt}\,B,\ E_{F_1,S_{\mathbb Q}})\bigr)\longrightarrow \mathtt{continuousH2S}\ S\ M$$ be additive and satisfy the predicate `IsGlobalBridge₂` for $S$, the restriction map $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to\mathrm{Gal}(F_1/\mathbb Q)$, the map [`Rep.relationModuleInt.ι B`](def/GroupCohomology_RelationModule.html#L75), the free cover [`Rep.freeCover B`](def/GroupCohomology_RelationModule.html#L15), the action on $\overline{\mathbb Q}^{\times}$, $\iota_{E_1}$ and $\kappa$; here `continuousH2S S M` is the quotient of `levelCocyclesS₂ S M` by the elements of it lying in `levelCoboundariesS₂ S M`. The assertion: there exists an intermediate field $F_2\supseteq F_1$, finite and Galois over $\mathbb Q$ and unramified outside $S$ in the above sense, such that for every intermediate field $F_3\supseteq F_2$ which is a number field Galois over $\mathbb Q$, every homomorphism $\pi\colon\mathrm{Gal}(F_3/\mathbb Q)\to\mathrm{Gal}(F_1/\mathbb Q)$ compatible with restriction from $\overline{\mathbb Q}$, every $\iota_{E_3}$ induced by $F_3\hookrightarrow\overline{\mathbb Q}$ as above, and every morphism $j_E$ from the $\pi$-restriction of $E_{F_1,S_{\mathbb Q}}$ to $E_{F_3,S_{\mathbb Q}}$ with $\iota_{E_3}\circ j_E=\iota_{E_1}$, any class $x$ with $\Lambda_1 x=0$ is killed by the degree-one cohomology map along $\pi$ and [`Rep.extInflR π B`](def/GroupCohomology_RelationHomDefect.html#L72) applied to $j_E$.
--
--   This is the Kummer step in Milne's proof of the global duality statement Arithmetic Duality Theorems I, Lemma 4.12 and Theorem 4.10: the kernel of the degree-two bridge $\mathrm{Ext}^2(B,E_S)\to H^2_S(M)$ at a fixed finite Galois level becomes zero after inflation to a suitable larger finite Galois level, unramified outside $S$, here recorded as an existence statement about that level. It feeds the construction of a nondegenerate pairing between the degree-one and degree-two Tate–Shafarevich groups of $M$ and its dual twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_SUnits_exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationHomDefect
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_GroupCohomology_GlobalBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain ExtCitation
open groupCohomology
open scoped NumberField.PlaceDecomp

theorem NumberField.SUnits.exists_level_forall_map_extInflR_eq_zero_of_isGlobalBridge2_apply_eq_zero
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F₁ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₁] [IsGalois ℚ ↥F₁] (hF₁ : F₁.IsUnramifiedOutside S)
    (hFM : ∀ s ∈ F₁.fixingSubgroup, ∀ m : M, M.ρ s m = m)
    (B : Rep ℤ (↥F₁ ≃ₐ[ℚ] ↥F₁)) [Fintype B] (hB : ∀ b : B, p • b = 0)

    (ιE₁ : NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE₁ : ∀ x, Additive.toMul (ιE₁ x) = Units.map (algebraMap ↥F₁ (AlgebraicClosure ℚ) : ↥F₁ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₁ Sℚ x))
    (hμ : ∀ u : (AlgebraicClosure ℚ)ˣ, u ^ p = 1 → ∃ e : NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ, ιE₁ e = Additive.ofMul u)

    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F₁ γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)

    {Λ₁ : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ)) →+ continuousH2S S M}
    (hΛ₁ : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F₁) (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE₁ κ Λ₁) :
    ∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), F₁ ≤ F₂ ∧ FiniteDimensional ℚ ↥F₂ ∧ IsGalois ℚ ↥F₂ ∧ F₂.IsUnramifiedOutside S ∧
      ∀ (F₃ : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F₃] [IsGalois ℚ ↥F₃] (_ : F₂ ≤ F₃)
        (π : (↥F₃ ≃ₐ[ℚ] ↥F₃) →* (↥F₁ ≃ₐ[ℚ] ↥F₁))
        (_ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π (AlgEquiv.restrictNormalHom ↥F₃ σ) = AlgEquiv.restrictNormalHom ↥F₁ σ)
        (ιE₃ : NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
        (_ : ∀ x, Additive.toMul (ιE₃ x) = Units.map (algebraMap ↥F₃ (AlgebraicClosure ℚ) : ↥F₃ →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F₃ Sℚ x))
        (jE : Rep.res π (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ) ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ)
        (_ : ∀ x, ιE₃ (jE.hom x) = ιE₁ x)
        (x : H1 ((ihom (Rep.relationModuleInt B)).obj (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ))) (_ : Λ₁ x = 0),
        (groupCohomology.map π (Rep.extInflR π B (NumberField.SUnits.sUnitsRep ℚ ↥F₁ Sℚ) (NumberField.SUnits.sUnitsRep ℚ ↥F₃ Sℚ) jE) 1).hom x = 0 := by sorry
