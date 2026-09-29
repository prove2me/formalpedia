-- Prove2me | Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_pos_forall_integral_ker_idelicNorm_eq_mul_integral_haarQuotient_unitsAct_mul_inv
-- name    : M4aHerbrand.IdeleGaloisDescent.exists_pos_forall_integral_ker_idelicNorm_eq_mul_integral_haarQuotient_unitsAct_mul_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/507d9004-601a-5b22-b47b-cd9f9ffbe404
-- title:
--   Haar transport along z ↦ σ(z)z⁻¹ for norm-one ideles
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite Galois, and equip the idele group $(\mathbb{A}_L)^\times$ with a measurable structure that is the Borel structure of its topology and with a Haar measure $\nu_{Z_L}$. Let $D$ be an idelic Galois descent datum for $L/K$, that is, a monoid homomorphism from $L \simeq_{\mathrm{alg}[K]} L$ to the ring automorphisms of $\mathbb{A}_L$ which is continuous in each component and agrees with the Galois action on the image of $L$; write $D.\mathrm{unitsAct}\,\sigma$ for the induced automorphism of $(\mathbb{A}_L)^\times$. Let $\sigma$ be an element of $\mathrm{Gal}(L/K)$ such that every $\tau$ lies in the subgroup of integer powers of $\sigma$. Let $A_K$ be a closed subgroup of $(\mathbb{A}_L)^\times$ whose elements are exactly the images of ideles of $K$ under the map induced on units by the ring homomorphism $\beta$ of the base-change datum `genuineBaseChange K L`, carrying a Haar measure $\mu_{A_K}$, and let $N_1$ be a closed subgroup whose elements are exactly the $z$ with $\beta$-relative idelic norm (the unit map of the algebra norm $\mathbb{A}_L \to \mathbb{A}_K$) equal to $1$, carrying a Haar measure $\mu_N$. Then there exists a real $c_N > 0$ such that for every function $g \colon (\mathbb{A}_L)^\times \to \mathbb{C}$, $\int_{N_1} g \, d\mu_N = c_N \int g\bigl((D.\mathrm{unitsAct}\,\sigma)(q.\mathrm{out}) \cdot (q.\mathrm{out})^{-1}\bigr)$, the second integral being over the orbit quotient of $(\mathbb{A}_L)^\times$ by $A_K$ against the measure [`HaarQuotient.measure`](def/HaarQuotient.html#L28) $\nu_{Z_L}\,A_K\,\mu_{A_K}$, i.e. the pushforward along the quotient map of $\nu_{Z_L}$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25), and $q.\mathrm{out}$ a chosen representative of the class $q$. No measurability or integrability hypothesis is imposed on $g$.
--
--   This is the measure-theoretic form of Hilbert's theorem 90 for ideles in a cyclic extension: the map $z \mapsto \sigma(z)z^{-1}$ identifies $A_K \backslash (\mathbb{A}_L)^\times$ with the norm-one ideles, and the identity records that Haar measure on the norm-one subgroup agrees, up to one positive constant, with the quotient measure transported along that map. The existence statement supplies the constant consumed by the twisted orbital integral computations in the automorphic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_IdeleGaloisDescent_exists_pos_forall_integral_ker_idelicNorm_eq_mul_integral_haarQuotient_unitsAct_mul_inv.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem M4aHerbrand.IdeleGaloisDescent.exists_pos_forall_integral_ker_idelicNorm_eq_mul_integral_haarQuotient_unitsAct_mul_inv
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure] :
    ∃ cN : ℝ, 0 < cN ∧
      ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
        ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
          cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
            g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK) := by sorry
