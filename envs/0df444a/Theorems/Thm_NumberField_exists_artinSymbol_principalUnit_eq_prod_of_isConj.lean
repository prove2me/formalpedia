-- Prove2me | Theorems.Thm_NumberField_exists_artinSymbol_principalUnit_eq_prod_of_isConj
-- name    : NumberField.exists_artinSymbol_principalUnit_eq_prod_of_isConj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/7520f57e-2c06-56d3-a30f-b4123e24e08b
-- title:
--   Artin symbol of a principal ideal congruent to 1
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ that is Galois, and suppose the Galois group $L \simeq_{\mathrm{alg}[K]} L$ is commutative. Then there is an ideal $\mathfrak f \neq 0$ of $\mathcal O_K$ with the following two properties. First, for every height-one prime $v$ of $\mathcal O_K$ whose ideal does not divide $\mathfrak f$ and every prime ideal $Q$ of $\mathcal O_L$ with $Q \cap \mathcal O_K = v$, the inertia subgroup of $Q$ inside $\mathrm{Gal}(L/K)$ is trivial. Second, let $\alpha \in \mathcal O_K$ be non-zero, let $\mathfrak m$ be an ideal of $\mathcal O_K$, and assume the principal fractional ideal $(\alpha)$, viewed as a unit of the group of fractional ideals of $\mathcal O_K$, lies in the subgroup `coprimeToModulus K 𝔪` of those units whose multiplicity at each prime dividing $\mathfrak m$ vanishes; let $c$ assign to each real embedding $\tau : K \to \mathbb R$ an element $c_\tau \in \mathrm{Gal}(L/K)$. If $\alpha - 1 \in \mathfrak f$ and if for every such $\tau$ there is a ring homomorphism $\varphi : L \to \mathbb C$ restricting to $\tau$ on $K$ for which $c_\tau$ is a conjugation element of $\varphi$ in the sense of `ComplexEmbedding.IsConj`, then the Artin symbol `artinSymbol K L 𝔪` — the homomorphism on the units coprime to $\mathfrak m$ built from the family $v \mapsto$ `artinFrob K L v` of arithmetic Frobenius elements at the chosen primes of $\mathcal O_L$ above $v$ — sends $(\alpha)$ to $\prod_{\tau(\alpha) < 0} c_\tau$, the product over the real embeddings $\tau$ of $K$ with $\tau(\alpha)$ negative.
--
--   This is Artin's reciprocity law for principal ideals of an abelian extension with the archimedean contributions made explicit: up to a conductor-like ideal $\mathfrak f$ dividing the modulus, the Artin symbol of $(\alpha)$ with $\alpha \equiv 1 \pmod{\mathfrak f}$ is the product of the complex conjugations at the real places of $K$ where $\alpha$ is negative, and in particular is trivial for totally positive $\alpha$. It underlies the computations of Artin symbols on principal units used in the Langlands–Tunnell part of the development, in particular the construction of an admissible twist of a Hecke character matching the determinant of an induced two-dimensional representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_artinSymbol_principalUnit_eq_prod_of_isConj.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply LanglandsTunnell.P2.Artin
open scoped IsMulCommutative

universe u v

theorem NumberField.exists_artinSymbol_principalUnit_eq_prod_of_isConj
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] :
    ∃ 𝔣 : Ideal (𝓞 K), 𝔣 ≠ ⊥ ∧
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 →
        ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.under (𝓞 K) = v.asIdeal →
          Q.inertia (L ≃ₐ[K] L) = ⊥) ∧
      (∀ (α : 𝓞 K) (hα : α ≠ 0) (𝔪 : Ideal (𝓞 K))
        (hc : principalUnit K α hα ∈ coprimeToModulus K 𝔪) (c : (K →+* ℝ) → (L ≃ₐ[K] L)),
        α - 1 ∈ 𝔣 →
        (∀ τ : K →+* ℝ, ∃ φ : L →+* ℂ,
          (∀ x : K, φ (algebraMap K L x) = τ x) ∧ ComplexEmbedding.IsConj φ (c τ)) →
        artinSymbol K L 𝔪 ⟨principalUnit K α hα, hc⟩ =
          ∏ τ ∈ Finset.univ.filter (fun τ : K →+* ℝ => τ (algebraMap (𝓞 K) K α) < 0), c τ) := by sorry
