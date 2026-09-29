-- Prove2me | Theorems.Thm_NumberField_Idele_exists_finset_forall_semiLocalCharacter_eq_one_and_eq_mul_prod_semiLocalCharacter_of_continuous
-- name    : NumberField.Idele.exists_finset_forall_semiLocalCharacter_eq_one_and_eq_mul_prod_semiLocalCharacter_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/c21b641c-5106-5e41-97ed-3c8a1a6eb97e
-- title:
--   Semi-local factorisation of a continuous idelic character
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $\xi_L$ be a monoid homomorphism from the full subgroup $\top$ of $(\mathbb{A}_L)^\times$, the units of `AdeleRing (𝓞 L) L`, to $\mathbb{C}^\times$, such that the composite $z \mapsto \xi_L(z) \in \mathbb{C}$ is continuous on $(\mathbb{A}_L)^\times$. Two conclusions are asserted. First, the function sending a unit $a$ of `InfiniteAdeleRing L` to $\xi_L(a,1) \in \mathbb{C}$, the value at the idele with infinite part $a$ and trivial finite part, is continuous. Secondly, there is a finite set $R$ of height-one primes of $\mathcal{O}_K$ with the following two properties. For $v \notin R$ and every unit $u$ of $L \otimes_K K_v$ lying in `integralUnits K L v`, the subgroup of units of the image submonoid of $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_v \to L \otimes_K K_v$, one has `semiLocalCharacter K L ξL v u` $=1$; here the semi-local character is the finite product, over the primes $w$ of $\mathcal{O}_L$ lying over $v$, of $\xi_L$ evaluated at the determinant of the $\mathrm{GL}_2$-element `heckeGenAt` attached to the $w$-component of $u$ under the base-change isomorphism $L \otimes_K K_v \cong \prod_{w \mid v} L_w$. Moreover, for every finite $S \supseteq R$ and every idele $t$ whose semi-local component `semiLocalIdele K L v t` (the image of the finite part of $t$ under evaluation at the primes above $v$) is integral in the above sense for all $v \notin S$, one has $\xi_L(t) = \xi_L(t_\infty,1) \cdot \prod_{v \in S}$ `semiLocalCharacter K L ξL v (semiLocalIdele K L v t)`, where $t_\infty$ is the infinite part of $t$.
--
--   This is the standard fact that a continuous character of the idele group of $L$ is unramified outside a finite set of places and factors as the product of its archimedean part and of its semi-local components, here organised relative to the base field $K$ and phrased through the determinants of the $\mathrm{GL}_2$ Hecke generators. It is used in the analysis of twisted orbital integrals, being cited by [`AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_exists_finset_forall_semiLocalCharacter_eq_one_and_eq_mul_prod_semiLocalCharacter_of_continuous.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem NumberField.Idele.exists_finset_forall_semiLocalCharacter_eq_one_and_eq_mul_prod_semiLocalCharacter_of_continuous
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) :
    Continuous (fun a : (InfiniteAdeleRing L)ˣ =>
        ((ξL ⟨Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) a,
          Subgroup.mem_top _⟩ : ℂˣ) : ℂ)) ∧
    ∃ R : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ R →
        ∀ u : (L ⊗[K] v.adicCompletion K)ˣ, u ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v →
          TwistedUnipotentTerm.semiLocalCharacter K L ξL v u = 1) ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), R ⊆ S →
        ∀ t : (AdeleRing (𝓞 L) L)ˣ,
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
            AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
              AutomorphicForm.TransversalMeasure.integralUnits K L v) →
          ((ξL ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ) =
            ((ξL ⟨Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))
                (Units.map (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).toMonoidHom t),
              Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
            ∏ v ∈ S, TwistedUnipotentTerm.semiLocalCharacter K L ξL v
              (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t) := by sorry
