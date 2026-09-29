-- Prove2me | Theorems.Thm_NumberField_AdelicHaar_adelicAddHaar_setOf_snd_apply_eq_zero
-- name    : NumberField.AdelicHaar.adelicAddHaar_setOf_snd_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/a4eb1481-74a2-5226-b07a-07eda3c7f06e
-- title:
--   Adeles vanishing at a fixed finite place form a null set
-- statement:
--   Let $F$ be a number field and let $v$ be a point of the height-one spectrum of its ring of integers $\mathcal{O}_F$, i.e. a nonzero prime ideal. Equip the adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, which is by construction the product of the infinite adele ring and the finite adele ring, with the Borel $\sigma$-algebra of its topology (`adeleBorel`) and with the additive Haar measure `adelicAddHaar (𝓞 F) F`, defined as Mathlib's `Measure.addHaar` for that Borel structure. The assertion is that the set of adeles $x$ whose finite component $x.2$ has vanishing $v$-coordinate, $\{x \in \mathbb{A}_F : x_v = 0\}$, has measure zero for this Haar measure. No hypotheses beyond $F$ being a number field and $v$ a nonzero prime of $\mathcal{O}_F$ are imposed; note that the condition constrains only the $v$-component of the finite part of $x$, all other components, finite and infinite, being unrestricted.
--
--   This is the standard fact that a coordinate hyperplane of the adele ring is Haar-null, the completion $F_v$ being non-discrete. It serves to discard the exceptional locus in changes of variables of the form $x_v \mapsto x_v^{-1}$, and is used in the analysis of adelic intertwining integrals for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicHaar_adelicAddHaar_setOf_snd_apply_eq_zero.lean

import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain

theorem NumberField.AdelicHaar.adelicAddHaar_setOf_snd_apply_eq_zero
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    adelicAddHaar (𝓞 F) F {x : AdeleRing (𝓞 F) F | x.2 v = 0} = 0 := by sorry
