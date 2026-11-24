-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PlusPolynomialInclusion_classParam_of_CM
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.classParam_of_CM
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:17.568189+00:00
-- url     : https://prove2.me/theorems/51bae092-9b00-4579-a04c-f683e9748e9b
-- title:
--   Plus Polynomial Inclusion: class Param of CM
-- statement:
--   The Plus Polynomial Inclusion construction uses the class Param of CM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/PlusPolynomialInclusion.lean#L173-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/PlusPolynomialInclusion.lean#L173-L174

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix NumberField IsDedekindDomain Formalism.UG
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
variable (k : Type) [Field k] [Algebra F k]
attribute [local instance] algLk
variable {k}
variable (k)

theorem GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.classParam_of_CM (h : ClassParamCM) : ClassParam := by sorry
