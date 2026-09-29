-- Prove2me | Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_continuousAddEquiv_measurePreserving_act_sub_algebraMap_mul_of_norm_ne_one
-- name    : M4aHerbrand.IdeleGaloisDescent.exists_continuousAddEquiv_measurePreserving_act_sub_algebraMap_mul_of_norm_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/6392b886-75ef-5e15-aebf-3b664712b263
-- title:
--   Measure-preserving twisted difference operator s ↦ σ(s) - cs on adeles
-- statement:
--   Let $K$ and $L$ be fields with $L$ a number field, $L$ an extension of $K$ that is finite-dimensional and Galois, and let $D$ be a datum of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is: a monoid homomorphism $D.\mathrm{act}$ from $L \simeq_{\mathrm{alg}[K]} L$ to the ring automorphisms of the adele ring $\mathbb{A}_L$ of $L$ (formed from $\mathcal{O}_L$ and $L$), such that for every $g$ in the Galois group and every $x \in L$ one has $D.\mathrm{act}(g)$ applied to the principal adele of $x$ equal to the principal adele of $g(x)$, and such that each $D.\mathrm{act}(g)$ is continuous. Let $\sigma$ be an element of the Galois group such that every $\tau$ lies in the subgroup of integer powers of $\sigma$, let $c \in L$ satisfy $\mathrm{N}_{L/K}(c) \neq 1$, and let $\mu$ be an additive Haar measure on $\mathbb{A}_L$, equipped with its Borel measurable structure. Then there exists a homeomorphic additive group isomorphism $e$ of $\mathbb{A}_L$ with itself such that $e(s) = D.\mathrm{act}(\sigma)(s) - c\,s$ for all $s \in \mathbb{A}_L$ (the product taken with the principal adele of $c$), such that the additive Haar character `addEquivAddHaarChar e` equals $1$, and such that $e$ preserves $\mu$.
--
--   This is the adelic twisted difference operator attached to a cyclic extension and a scalar of norm $\neq 1$; the bijectivity half is the adelic form of a lemma of Langlands in the theory of base change for $\mathrm{GL}(2)$, and the statement packages it together with the assertion that the resulting topological group automorphism has modulus $1$, hence preserves every additive Haar measure. It is used in the change-of-variables steps for twisted orbital integrals over unipotent subgroups of $\mathrm{GL}(2)$ that appear in the comparison of trace formulae.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_IdeleGaloisDescent_exists_continuousAddEquiv_measurePreserving_act_sub_algebraMap_mul_of_norm_ne_one.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory

theorem M4aHerbrand.IdeleGaloisDescent.exists_continuousAddEquiv_measurePreserving_act_sub_algebraMap_mul_of_norm_ne_one
    {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : L) (hc : Algebra.norm K c ≠ 1)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 L) L)) [μ.IsAddHaarMeasure] :
    ∃ e : AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L,
      (∀ s : AdeleRing (𝓞 L) L,
        e s = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) s - algebraMap L (AdeleRing (𝓞 L) L) c * s) ∧
      MeasureTheory.addEquivAddHaarChar e = 1 ∧ MeasureTheory.MeasurePreserving e μ μ := by sorry
