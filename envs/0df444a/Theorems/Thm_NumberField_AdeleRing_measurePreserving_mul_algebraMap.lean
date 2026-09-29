-- Prove2me | Theorems.Thm_NumberField_AdeleRing_measurePreserving_mul_algebraMap
-- name    : NumberField.AdeleRing.measurePreserving_mul_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/da5abaa7-87a4-53f4-951e-4e182c17ef15
-- title:
--   Multiplication by a principal adele preserves additive Haar measure
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, equipped with a measurable space structure that makes it a Borel space (so the $\sigma$-algebra is the Borel one of its topology). Let $\mu$ be a measure on $\mathbb{A}_F$ which is an additive Haar measure (left-invariant for addition, positive on non-empty open sets, finite on compacts) and regular, and let $a \in F$ with $a \neq 0$. The conclusion is that the map $x \mapsto \iota(a)\,x$, where $\iota =$ `algebraMap F (AdeleRing (𝓞 F) F)` is the diagonal embedding of $F$ into its adele ring, is measure preserving from $(\mathbb{A}_F,\mu)$ to itself: it is measurable and its pushforward of $\mu$ is again $\mu$, equivalently $\mu(\{x : \iota(a)x \in S\}) = \mu(S)$ for all measurable $S$. The assertion is made for an arbitrary additive Haar measure, not only for a fixed normalised one, and the hypotheses on $\mu$ are exactly additive Haar-ness and regularity.
--
--   This is the measure-theoretic form of the product formula $\prod_v |a|_v = 1$ for a number field: the adelic modulus of a principal idele is $1$. It feeds the computation of the distributive Haar character of multiplication by a principal adele, [`NumberField.AdeleRing.distribHaarChar_algebraMap`](thm.html#NumberField.AdeleRing.distribHaarChar_algebraMap), and its specialisation to the normalised adelic Haar measure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_measurePreserving_mul_algebraMap.lean

import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField

theorem NumberField.AdeleRing.measurePreserving_mul_algebraMap (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] [μ.Regular]
    (a : F) (ha : a ≠ 0) :
    MeasureTheory.MeasurePreserving (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x) μ μ := by sorry
