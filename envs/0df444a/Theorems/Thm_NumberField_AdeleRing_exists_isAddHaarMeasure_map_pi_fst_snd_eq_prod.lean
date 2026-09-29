-- Prove2me | Theorems.Thm_NumberField_AdeleRing_exists_isAddHaarMeasure_map_pi_fst_snd_eq_prod
-- name    : NumberField.AdeleRing.exists_isAddHaarMeasure_map_pi_fst_snd_eq_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/f87db724-a033-5a3f-8aa6-e9371eae847e
-- title:
--   Haar measure on mathbb A_K^ι splits along K_∞^ι×mathbb A_{K,f}^ι
-- statement:
--   Let $K$ be a number field and $\iota$ a finite type, and recall that the adele ring $\mathbb A_K$ of $K$ is by construction the product $K_\infty\times\mathbb A_{K,f}$ of the infinite adele ring and the finite adele ring, so that the two coordinate projections are the first and second components. Fix measurable space structures on $\mathbb A_K$, on $K_\infty$ and on $\mathbb A_{K,f}$, each assumed to be the Borel $\sigma$-algebra of the respective topology, and let $\rho$ be an additive Haar measure on $\iota \to \mathbb A_K$ and $\nu$ an additive Haar measure on $\iota \to K_\infty$. The assertion is a conjunction of five statements: $K_\infty$ is second countable; $\mathbb A_{K,f}$ is second countable; the coordinate shuffle $a \mapsto ((a_k)_\infty{}_{,k\in\iota}, (a_k)_f{}_{,k\in\iota})$ from $\iota \to \mathbb A_K$ to $(\iota \to K_\infty) \times (\iota \to \mathbb A_{K,f})$ is measurable; its inverse $p \mapsto (k \mapsto (p_1(k), p_2(k)))$, viewed as a map into $\iota \to \mathbb A_K$, is measurable; and there exists an additive Haar measure $\nu'$ on $\iota \to \mathbb A_{K,f}$ such that the pushforward of $\rho$ along the coordinate shuffle equals the product measure $\nu \times \nu'$. The measurability claims are with respect to the product $\sigma$-algebras induced by the given Borel structures.
--
--   This is the measure-theoretic form of the standard splitting $\mathbb A_K = K_\infty \times \mathbb A_{K,f}$ of Haar measure on a finite power of the adele ring, with the archimedean factor prescribed in advance and the finite-adelic factor produced by uniqueness of Haar measure up to a positive scalar. It is used in the analytic bookkeeping for adelic automorphic forms, where volumes of adelic boxes and integrals against Schwartz functions on the archimedean part are compared with measures of level subgroups and preimages on the finite part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_exists_isAddHaarMeasure_map_pi_fst_snd_eq_prod.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem NumberField.AdeleRing.exists_isAddHaarMeasure_map_pi_fst_snd_eq_prod
    (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
    (ρ : Measure (ι → AdeleRing (𝓞 K) K)) [ρ.IsAddHaarMeasure]
    (ν : Measure (ι → InfiniteAdeleRing K)) [ν.IsAddHaarMeasure] :
    SecondCountableTopology (InfiniteAdeleRing K) ∧ SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) ∧
    Measurable (fun a : ι → AdeleRing (𝓞 K) K => ((fun k => (a k).1), (fun k => (a k).2))) ∧
    Measurable (β := ι → AdeleRing (𝓞 K) K)
      (fun p : (ι → InfiniteAdeleRing K) × (ι → FiniteAdeleRing (𝓞 K) K) => fun k => (p.1 k, p.2 k)) ∧
    ∃ ν' : Measure (ι → FiniteAdeleRing (𝓞 K) K), ν'.IsAddHaarMeasure ∧
      Measure.map (fun a : ι → AdeleRing (𝓞 K) K => ((fun k => (a k).1), (fun k => (a k).2))) ρ =
        ν.prod ν' := by sorry
