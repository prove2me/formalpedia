-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PlusPolynomialInclusion_alpha_val
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.alpha_val
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:15:14.156029+00:00
-- url     : https://prove2.me/theorems/670e06c1-af49-4685-8991-c670f9ab5516
-- title:
--   Plus Polynomial Inclusion: alpha val
-- statement:
--   The Plus Polynomial Inclusion construction uses the alpha val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/PlusPolynomialInclusion.lean#L29-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/PlusPolynomialInclusion.lean#L29-L29

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.alpha_val (hP : IsPPol c r P) : (alpha hP : AdjoinRoot P) = AdjoinRoot.root P := by sorry
