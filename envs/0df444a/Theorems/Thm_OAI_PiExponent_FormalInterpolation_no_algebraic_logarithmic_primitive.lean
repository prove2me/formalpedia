-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_no_algebraic_logarithmic_primitive
-- name    : OAI.PiExponent.FormalInterpolation.no_algebraic_logarithmic_primitive
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T23:27:13.634207+00:00
-- url     : https://prove2.me/theorems/48f7595f-66fd-45ce-be71-9beed29f85b7
-- title:
--   A finitely generated complex function field has no nonconstant logarithmic primitive
-- statement:
--   This supplies an independent field-theoretic route to the manuscript's residue obstruction. For y=0 choose a=0; algebraic y is constant because Complex is algebraically closed. Otherwise extend y to a transcendence basis. E is finite separable over its rational function field L. Extend the Euler derivation y*d/dy from L to E; the hypothesis gives D(z)=1. Commutation of trace and derivation gives y*d/dy(Tr(z))=[E:L]. A rational function in y over the field of the remaining basis elements has zero constant Laurent coefficient after applying y*d/dy, contradicting the nonzero characteristic-zero degree. The statement retains finite generation but requires neither transcendence degree one nor curve-place data.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.no_algebraic_logarithmic_primitive
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (y z : E)
    (hprimitive : ∀ D : Derivation Complex E E, D z = D y / y) :
    ∃ a : Complex, y = algebraMap Complex E a := by sorry
