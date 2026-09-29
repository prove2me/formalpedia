-- Prove2me | Theorems.Thm_NumberField_exists_completedRayL_functionalEquation_of_primitive
-- name    : NumberField.exists_completedRayL_functionalEquation_of_primitive
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/20eaffa1-0439-5da2-b434-e3ef0f6a0a58
-- title:
--   Hecke's functional equation for primitive narrow ray class characters
-- statement:
--   Let $K$ be a number field, let $\mathfrak f \neq 0$ be an ideal of $\mathcal O_K$, let $\chi$ be a monoid homomorphism from the narrow ray class group $\mathrm{Cl}_{\mathfrak f}^{+}(K)$ (the group of invertible fractional ideals whose valuation count vanishes at every height-one prime dividing $\mathfrak f$, modulo the subgroup `narrowRaySubgroup K 𝔣`) to $\mathbb C$, and let $S$ be a finite set of real infinite places of $K$. Two hypotheses are imposed. Parity: for every $\alpha \in \mathcal O_K$, $\alpha \neq 0$, whose principal ideal is coprime to $\mathfrak f$ in the above sense and which satisfies $\alpha - 1 \in \mathfrak f$, the value of $\chi$ on the class of $(\alpha)$ equals $\prod_{w \in S} \operatorname{sign}(w(\alpha))$, the signs being taken under the real embeddings attached to the places in $S$. Primitivity: for every ideal $\mathfrak f' \supsetneq \mathfrak f$ there is a non-zero $\alpha \in \mathcal O_K$ with $(\alpha)$ coprime to $\mathfrak f$, $\alpha - 1 \in \mathfrak f'$, $\tau(\alpha) > 0$ for every ring homomorphism $\tau : K \to \mathbb R$, and $\chi([(\alpha)]) \neq 1$. The conclusion asserts the existence of $W \in \mathbb C$, $W \neq 0$, and of two entire functions $\Lambda, \Lambda'$ on $\mathbb C$ such that, for $\operatorname{Re}(s) > 1$, $\Lambda(s) = P(s)\,\Lambda_{\mathfrak f,S}(s,\chi)$ and $\Lambda'(s) = P(s)\,\Lambda_{\mathfrak f,S}(s,\bar\chi)$, where $P(s) = s(s-1)$ if $\chi = 1$ and $P(s) = 1$ otherwise, $\bar\chi$ is $\chi$ composed with complex conjugation, and $\Lambda_{\mathfrak f,S}(s,\psi) = (|d_K|\,N\mathfrak f)^{s/2}\,\Gamma_{\mathbb R}(s)^{r_1 - \#S}\,\Gamma_{\mathbb R}(s+1)^{\#S}\,\Gamma_{\mathbb C}(s)^{r_2}\sum_{C}\psi(C)\,\mathrm{rayZeta}_{\mathfrak f}(C,s)$ is [`M4aTorus.completedRayL`](def/NumberField_CompletedRayL.html#L26), the sum running over the narrow ray classes modulo $\mathfrak f$; and such that $\Lambda(1-s) = W\,\Lambda'(s)$ for every $s \in \mathbb C$.
--
--   This is Hecke's functional equation for the completed $L$-function of a primitive narrow ray class character of conductor $\mathfrak f\cdot\infty_S$, in the form asserting entirety after multiplication by $s(s-1)$ in the trivial-character case and a non-zero root number $W$. It feeds the corresponding statement for abelian Artin $L$-functions, [`ArtinL.Abelian.exists_completedLSeries_functionalEquation_u0`](thm.html#ArtinL.Abelian.exists_completedLSeries_functionalEquation_u0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_completedRayL_functionalEquation_of_primitive.lean

import Mathlib
import Definitions.Def_NumberField_CompletedRayL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace Deep.NTSupply

universe u

open scoped Classical in

theorem NumberField.exists_completedRayL_functionalEquation_of_primitive
    (K : Type u) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (S : Finset {w : InfinitePlace K // w.IsReal})
    (hpar : ∀ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
      α - 1 ∈ 𝔣 →
        χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) =
          ∏ w ∈ S, ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ))
    (hprim : ∀ 𝔣' : Ideal (𝓞 K), 𝔣 ≤ 𝔣' → 𝔣' ≠ 𝔣 →
      ∃ (α : 𝓞 K) (hα : α ≠ 0) (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔣),
        α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
          χ (NarrowRayClassGroup.mk K 𝔣 ⟨principalUnit K α hα, hc⟩) ≠ 1) :
    ∃ (W : ℂ) (Λ Λ' : ℂ → ℂ), W ≠ 0 ∧ Differentiable ℂ Λ ∧ Differentiable ℂ Λ' ∧
      (∀ s : ℂ, 1 < s.re →
        Λ s = (if χ = 1 then s * (s - 1) else 1) * M4aTorus.completedRayL K 𝔣 χ S s ∧
        Λ' s = (if χ = 1 then s * (s - 1) else 1) *
          M4aTorus.completedRayL K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S s) ∧
      (∀ s : ℂ, Λ (1 - s) = W * Λ' s) := by sorry
