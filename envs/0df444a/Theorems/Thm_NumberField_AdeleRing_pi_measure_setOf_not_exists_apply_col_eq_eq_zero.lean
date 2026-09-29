-- Prove2me | Theorems.Thm_NumberField_AdeleRing_pi_measure_setOf_not_exists_apply_col_eq_eq_zero
-- name    : NumberField.AdeleRing.pi_measure_setOf_not_exists_apply_col_eq_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/4383162e-20f6-57ac-8f57-16dfc047556e
-- title:
--   Almost every adelic pair is a unimodular column
-- statement:
--   Let $K$ be a number field (a field, of type `Type`, with a `NumberField` instance), and write $\mathbb{A} =$ `AdeleRing (𝓞 K) K` for its adele ring, equipped with a measurable space structure which is assumed to be the Borel $\sigma$-algebra of its topology. Let $\mu$ be a measure on $\mathbb{A}$ which is an additive Haar measure, i.e. `μ.IsAddHaarMeasure` holds. Consider the product measure $\mu \otimes \mu$ on $\mathbb{A}^2$, formalised as `Measure.pi` of the constant family indexed by `Fin 2`. The assertion is that the set of those $c : \mathrm{Fin}\,2 \to \mathbb{A}$ for which there exists no $g \in \mathrm{GL}_2(\mathbb{A})$ whose underlying $2 \times 2$ matrix has first column equal to $c$ — that is, with $i \mapsto g_{i,0}$ equal to $c$ as a function — has product measure zero. Equivalently, $\mu \otimes \mu$-almost every pair of adeles is the first column of an invertible adelic $2 \times 2$ matrix, i.e. is unimodular.
--
--   This is the adelic statement that non-unimodular columns form a null set, the measure-theoretic input allowing integrals over $\mathbb{A}^2$ to be replaced by integrals over $\mathrm{GL}_2(\mathbb{A})$-columns. It is used in the theory of automorphic forms on $\mathrm{GL}_2$ over the adeles, in the comparison of an integral over the adelic plane with an integral involving the idele norm and the determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_pi_measure_setOf_not_exists_apply_col_eq_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem NumberField.AdeleRing.pi_measure_setOf_not_exists_apply_col_eq_eq_zero
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure) :
    (Measure.pi fun _ : Fin 2 => μ)
      {c : Fin 2 → AdeleRing (𝓞 K) K | ¬ ∃ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0) = c} = 0 := by sorry
