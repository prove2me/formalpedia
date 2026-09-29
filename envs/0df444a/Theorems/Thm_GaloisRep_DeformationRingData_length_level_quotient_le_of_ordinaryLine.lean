-- Prove2me | Theorems.Thm_GaloisRep_DeformationRingData_length_level_quotient_le_of_ordinaryLine
-- name    : GaloisRep.DeformationRingData.length_level_quotient_le_of_ordinaryLine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/a6f295f9-1456-5e8e-b414-affb252bfc27
-- title:
--   Per-level cotangent bound by ℓ(𝒪/(α²-1)) at the ordinary line
-- statement:
--   Let $\mathcal O$ be a complete discrete valuation ring (a domain, adically complete for its maximal ideal), $\bar\rho$ a two-dimensional residual Galois representation over the residue field of $\mathcal O$, and $\mathcal D_0,\mathcal D'$ two deformation conditions, i.e. predicates on adic Galois representations over local $\mathcal O$-algebras. Let $D_0$ and $D'$ be `DeformationRingData` for $\bar\rho$ with conditions $\mathcal D_0$ and $\mathcal D'$ — universal couples consisting of a complete noetherian local $\mathcal O$-algebra $R$, a representation of its type with residual representation equivalent to $\bar\rho$, and the universal property — and let $\theta : D'.R \to D_0.R$ and $x_0 : D_0.R \to \mathcal O$ be $\mathcal O$-algebra maps that are local homomorphisms, with $\theta$ surjective. Let $p$ be an odd prime with $p$ in the maximal ideal of $\mathcal O$, assume the base change of $D_0.\rho$ along $x_0$ is flat at $p$ in the sense of `IsFlatAt` (realisation of each finite level as the points of a finite flat commutative cocommutative Hopf algebra over the localisation at $p$), and assume the base change of $D'.\rho$ along $\theta$ is equivalent to $D_0.\rho$. Write $V$ for the underlying module of the base change of $D_0.\rho$ along $x_0$. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit in $P$, and let $L \subseteq V$ be an $\mathcal O$-submodule of the form $\mathcal O\cdot b_0$ for some basis $(b_0,b_1)$ of $V$, stable under the decomposition subgroup of $P$ over $\mathbb Q$, with the inertia subgroup acting trivially on $V/L$, and let $\alpha \in \mathcal O$ be such that every element of the decomposition subgroup that is a Frobenius at $p$ (acting as $x \mapsto x^p$ on the residue field of $P$) acts on $V/L$ by $\alpha$. Assume further that every $\mathcal D'$-representation has cyclotomic determinant at $p$ and is ordinary at $p$ in the sense of `IsOrdinaryAt`, that $\mathcal D'$ is stable under base change along local homomorphisms of local $\mathcal O$-algebras, and that a $\mathcal D'$-representation which is flat at $p$ satisfies $\mathcal D_0$. Then for every $n \in \mathbb N$, the $\mathcal O$-length of $\mathrm{Hom}_{\mathcal O}(\Phi',\mathcal O/\mathfrak m^{n+1})$, where $\Phi'$ is the cotangent module of $\ker(x_0 \circ \theta)$, modulo the submodule of functionals vanishing on the kernel of the map $\Phi' \to \ker(x_0)$-cotangent induced by $\theta$, is at most the $\mathcal O$-length of $\mathcal O/(\alpha^2-1)$.
--
--   This is the per-level form, at the prime $p$ itself, of the bound comparing the ordinary (Selmer) cotangent space with the flat one, as in Wiles' Chapter 1 and in the Darmon–Diamond–Taylor account of the numerical criterion; the bounding quantity $\ell_{\mathcal O}(\mathcal O/(\alpha^2-1))$ comes from the $\alpha$-action of Frobenius on the quotient $V/L$. It feeds the accumulation step [`GaloisRep.DeformationRingData.length_cotangent_le_add_of_ordinaryCondition_of_flatCondition`](thm.html#GaloisRep.DeformationRingData.length_cotangent_le_add_of_ordinaryCondition_of_flatCondition), which adds this contribution to the length of the flat cotangent module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_DeformationRingData_length_level_quotient_le_of_ordinaryLine.lean

import Mathlib
import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.BilinearMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem GaloisRep.DeformationRingData.length_level_quotient_le_of_ordinaryLine
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟₀ 𝒟' : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (D' : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟')
    (θ : D'.R →ₐ[𝒪] D₀.R) (x₀ : D₀.R →ₐ[𝒪] 𝒪)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hθ : IsLocalHom (θ : D'.R →+* D₀.R)) (hx₀ : IsLocalHom (x₀ : D₀.R →+* 𝒪))
    (hfl : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).IsFlatAt p)
    (hθρ : (D'.ρ.baseChangeAlong (θ : D'.R →+* D₀.R) hθ).IsEquiv D₀.ρ)
    (hθsurj : Function.Surjective θ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (L : Submodule 𝒪 (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V)
    (hLb : ∃ b : Module.Basis (Fin 2) 𝒪 (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V, L = 𝒪 ∙ b 0)
    (hLD : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L,
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v ∈ L)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V,
      (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v - v ∈ L)
    (α : 𝒪)
    (hα : ∀ σ ∈ P.decompositionSubgroup ℚ, P.IsFrobeniusAt σ p →
      ∀ v : (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).V,
        (D₀.ρ.baseChangeAlong (x₀ : D₀.R →+* 𝒪) hx₀).ρ σ v - α • v ∈ L)
    (Hdet : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.DetIsCyclotomic p)
    (H1 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A)
        {B : Type} [CommRing B] [IsLocalRing B] [Algebra 𝒪 B] (f : A →+* B) (hf : IsLocalHom f),
      𝒟' ρA → 𝒟' (ρA.baseChangeAlong f hf))
    (Hord : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsOrdinaryAt p)
    (H2 : ∀ {A : Type} [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρA : GaloisRepAdic A),
      𝒟' ρA → ρA.IsFlatAt p → 𝒟₀ ρA)
    (n : ℕ) :
    Module.length 𝒪 (((RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪)).Cotangent →ₗ[𝒪]
        𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1)) ⧸
      LinearMap.ker (LinearMap.lcomp 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ (n + 1))
        (LinearMap.ker (Ideal.mapCotangent (RingHom.ker (x₀.comp θ : D'.R →ₐ[𝒪] 𝒪))
            (RingHom.ker x₀) θ (fun _ hr => hr))).subtype)) ≤
    Module.length 𝒪 (𝒪 ⧸ Ideal.span {α ^ 2 - 1}) := by sorry
