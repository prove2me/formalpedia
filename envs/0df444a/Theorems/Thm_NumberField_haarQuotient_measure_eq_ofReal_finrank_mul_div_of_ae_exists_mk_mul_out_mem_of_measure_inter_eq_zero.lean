-- Prove2me | Theorems.Thm_NumberField_haarQuotient_measure_eq_ofReal_finrank_mul_div_of_ae_exists_mk_mul_out_mem_of_measure_inter_eq_zero
-- name    : NumberField.haarQuotient_measure_eq_ofReal_finrank_mul_div_of_ae_exists_mk_mul_out_mem_of_measure_inter_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/4bbf17ab-285f-5657-96a1-8897c2f2d898
-- title:
--   Covolume of L^×/K^× in A_L^×/A_K^×
-- statement:
--   Let $L/K$ be a finite Galois extension of number fields, and equip the idele unit groups $(\mathbb{A}_L)^\times$ and $(\mathbb{A}_K)^\times$ with Borel measurable structures and Haar measures $\nu_{Z,L}$, $\nu_{Z,K}$, together with sets $\Omega_L$, $\Omega_K$ that are fundamental domains for the actions of the images of the principal-idele maps $L^\times \to (\mathbb{A}_L)^\times$ and $K^\times \to (\mathbb{A}_K)^\times$ (the ranges of `Units.map (algebraMap …)`). Let $A_K \le (\mathbb{A}_L)^\times$ be a closed subgroup whose elements are exactly the images of units of $\mathbb{A}_K$ under the map induced on units by the ring homomorphism $\beta$ of [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87) (the adelic base-change datum, compatible with $K \to L$ on principal adeles and inducing $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$), and let $\mu_{A_K}$ be a Haar measure on $A_K$ such that for every $g : (\mathbb{A}_L)^\times \to \mathbb{C}$ the $\mu_{A_K}$-integral of $g$ over $A_K$ equals the $\nu_{Z,K}$-integral of $g$ composed with that induced map. Write $Q$ for [`HaarQuotient.measure νZL AK μAK`](def/HaarQuotient.html#L28), the push-forward along $(\mathbb{A}_L)^\times \to A_K\backslash(\mathbb{A}_L)^\times$ (the orbit quotient `MulAction.orbitRel.Quotient`) of $\nu_{Z,L}$ weighted by the density $g \mapsto \mathrm{weight}\,A_K\,\mu_{A_K}\,g$ divided by $\int^- _{x : A_K} \mathrm{weight}\,A_K\,\mu_{A_K}\,(x g)\,d\mu_{A_K}$. Let $F$ be a $Q$-null-measurable subset of the quotient such that for $Q$-almost every class $q$ there is $w \in L^\times$ with the class of $\iota(w)\cdot q.\mathrm{out}$ in $F$ (where $\iota$ is the principal-idele map on units), and such that for all $w, w' \in L^\times$ with $w^{-1}w'$ outside the image of $K^\times$ the sets $\{q \mid [\iota(w)^{-1} q.\mathrm{out}] \in F\}$ and $\{q \mid [\iota(w')^{-1} q.\mathrm{out}] \in F\}$ meet in a $Q$-null set. Then $Q(F)$ equals the extended-real value of $$[L:K]\cdot\frac{\nu_{Z,L}\bigl(\Omega_L \cap \{z \mid \|z\|_L \in [1, e]\}\bigr)}{\nu_{Z,K}\bigl(\Omega_K \cap \{a \mid \|a\|_K \in [1, e]\}\bigr)},$$ the measures being taken as reals, where $\|\cdot\|_F$ denotes [`NumberField.TateGlobal.ideleNorm F`](def/NumberField_TateGlobalZeta.html#L19), the value of the `distribHaarChar` of $\mathbb{A}_F$ at the given unit, viewed as a real number.
--
--   This is the covolume computation for the idele-class group of $L$ relative to that of $K$: a set of representatives for $L^\times/K^\times$ acting on $A_K\backslash(\mathbb{A}_L)^\times$ has quotient measure $[L:K]$ times the ratio of the unit-shell volumes of the two idele-class groups, the factor $[L:K]$ coming from $\|\beta(a)\|_L = \|a\|_K^{[L:K]}$. It is used in the proof of [`NumberField.measure_fundamentalDomain_range_div_eq_mul_finrank_mul_div_of_ker_idelicNorm`](thm.html#NumberField.measure_fundamentalDomain_range_div_eq_mul_finrank_mul_div_of_ker_idelicNorm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_haarQuotient_measure_eq_ofReal_finrank_mul_div_of_ae_exists_mk_mul_out_mem_of_measure_inter_eq_zero.lean

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_SigmaAdelicAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

theorem NumberField.haarQuotient_measure_eq_ofReal_finrank_mul_div_of_ae_exists_mk_mul_out_mem_of_measure_inter_eq_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)

    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (hμAK : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ a : AK, g (a : (AdeleRing (𝓞 L) L)ˣ) ∂μAK =
        ∫ a, g (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) ∂νZK)

    (F : Set (MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ))
    (hFm : NullMeasurableSet F (HaarQuotient.measure νZL AK μAK))
    (hFcov : ∀ᵐ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ ∂(HaarQuotient.measure νZL AK μAK), ∃ w : Lˣ,
      (Quotient.mk'' ((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈ F)
    (hFdisj : ∀ w w' : Lˣ, w⁻¹ * w' ∉ Set.range (Units.map (algebraMap K L : K →* L)) →
      HaarQuotient.measure νZL AK μAK
        ({q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ |
          (Quotient.mk'' (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w)⁻¹ * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈
            F} ∩
         {q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ |
          (Quotient.mk'' (((Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)) w')⁻¹ * q.out) : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ) ∈
            F}) = 0) :
    HaarQuotient.measure νZL AK μAK F =
      ENNReal.ofReal ((Module.finrank K L : ℝ) *
        (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal /
        (νZK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal) := by sorry
