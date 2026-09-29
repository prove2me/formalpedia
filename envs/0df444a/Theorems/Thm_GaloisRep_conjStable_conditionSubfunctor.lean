-- Prove2me | Theorems.Thm_GaloisRep_conjStable_conditionSubfunctor
-- name    : GaloisRep.conjStable_conditionSubfunctor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/10774a15-345c-5f14-be06-3c6189d313e8
-- title:
--   Conjugation-stability of the deformation-condition subfunctor
-- statement:
--   Fix a commutative local ring $\mathcal{O}$, and let $\mathcal{D}$ be a predicate assigning to every local commutative $\mathcal{O}$-algebra $A$ and every element of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16) — that is, a finite free $A$-module $V$ with $\operatorname{rank}_A V = 2$ together with a monoid homomorphism $\rho : \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \operatorname{End}_A(V)$ satisfying the adic continuity condition [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9) (for each $n$ some finite subextension $L/\mathbb{Q}$ acts trivially modulo $\mathfrak{m}_A^n V$) — a truth value. Let $\rho_0$ be a continuous homomorphism $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2$ of the residue field of $\mathcal{O}$ with its discrete topology, viewed as a point of `repnFunctor` at the terminal object `ProartinianCat.residueField`. The assertion is that the subfunctor [`GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀`](def/GaloisRep_ConditionLifts.html#L22) is [`Deformation.ConjStable`](def/Deformations_ConjQuotSubfunctor.html#L86): for every object $A$ of `ProartinianCat 𝒪` (a pro-artinian local topological $\mathcal{O}$-algebra which is a residue algebra over $\mathcal{O}$), every continuous $\rho' : \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(A)$ lying in that subfunctor at $A$, and every $\gamma \in \mathrm{ConjAct}(\mathrm{GL}_2(A))$ whose underlying matrix lies in the kernel of reduction $\mathrm{GL}_2(A) \to \mathrm{GL}_2$ of the residue field, the conjugate $\gamma \cdot \rho'$ again lies in the subfunctor at $A$. Membership at $A$ means two things: $\rho'$ pushes forward to $\rho_0$ along the map to the residue field, and for every artinian object $B$, every morphism $f : A \to B$, every $\rho_B \in$ [`GaloisRepAdic B`](def/GaloisRep_Adic.html#L16) and every $B$-basis $b$ of its module indexed by `Fin 2`, if the matrix of $\rho_B(\sigma)$ in $b$ equals the matrix of $(f_*\rho')(\sigma)$ for all $\sigma$, then $\mathcal{D}$ holds of $\rho_B$.
--
--   This is one of the hypotheses required to represent the quotient of a framed deformation functor by the kernel of reduction, in the style of Mazur's and Ramakrishna's deformation conditions: the subfunctor cut out by a condition $\mathcal{D}$ is stable under conjugation by matrices congruent to the identity modulo the maximal ideal. It is used in the construction of the deformation ring data, via [`GaloisRep.nonempty_deformationRingData`](thm.html#GaloisRep.nonempty_deformationRingData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_conjStable_conditionSubfunctor.lean

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory IsLocalRing

theorem GaloisRep.conjStable_conditionSubfunctor
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (Deformation.repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      Deformation.ProartinianCat.residueField) :
    Deformation.ConjStable (Fin 2) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀) := by sorry
