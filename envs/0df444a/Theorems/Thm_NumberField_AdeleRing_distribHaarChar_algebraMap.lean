-- Prove2me | Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
-- name    : NumberField.AdeleRing.distribHaarChar_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/701bce02-c2f2-5aab-90ed-605eaf3aa6c1
-- title:
--   Adelic modulus of a principal idele is 1
-- statement:
--   Let $F$ be a number field, with its ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, equipped with a measurable space structure which is assumed to be the Borel structure of its topology; and let $a$ be a unit of $F$, i.e. a nonzero element of $F$ viewed in $F^\times$. The assertion is that the value of Mathlib's distributive Haar character `MeasureTheory.distribHaarChar` of the additive group $\mathbb{A}_F$ — the homomorphism from the units of $\mathbb{A}_F$ to the positive reals characterised by $\mu(u\cdot S) = \mathrm{distribHaarChar}(u)\,\mu(S)$ for an additive Haar measure $\mu$ on $\mathbb{A}_F$ — at the idele obtained by pushing $a$ through the structure map $F \to \mathbb{A}_F$ (the diagonal embedding, applied to units via `Units.map`) equals $1$. Equivalently: scaling by a principal idele preserves additive Haar measure on $\mathbb{A}_F$, so $F^\times$ lies in the kernel of the adelic modulus.
--
--   This is the product formula $\prod_v |a|_v = 1$ for a number field, phrased as the triviality of the adelic modulus on principal ideles, so that $F^\times \subseteq \mathbb{A}_F^1$. It is the invariance statement underlying the $F^\times$-equivariance of adelic Fourier theory and of the idele class group constructions used further on in the automorphic part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdeleRing_distribHaarChar_algebraMap.lean

import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField

theorem NumberField.AdeleRing.distribHaarChar_algebraMap (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (a : Fˣ) :
    MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F)
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1 := by sorry
