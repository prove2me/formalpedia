-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PlusPolynomialInclusion_starL_of
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.starL_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:24.104634+00:00
-- url     : https://prove2.me/theorems/98ef0954-d365-4c4a-aeda-407580fc1451
-- title:
--   Plus Polynomial Inclusion: star L of
-- statement:
--   The Plus Polynomial Inclusion construction uses the star L of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/PlusPolynomialInclusion.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/PlusPolynomialInclusion.lean#L54-L56

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.starL_of (hP : IsPPol c r P) (e : E) :
    starL hP (AdjoinRoot.of P e) = AdjoinRoot.of P (c e) := by sorry
