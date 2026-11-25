-- Prove2me | Theorems.Thm_GlobalTheory_Published_cohDimTwoLocal_of_localFiniteness
-- name    : GlobalTheory.Published.cohDimTwoLocal_of_localFiniteness
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:09.401558+00:00
-- url     : https://prove2.me/theorems/5d75a49f-01b4-5671-93df-e0e121950b46
-- title:
--   Published: coh Dim Two Local of local Finiteness
-- statement:
--   The Published construction uses the coh Dim Two Local of local Finiteness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/CohDimTwoLocalOfLocalFiniteness.lean#L108-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/CohDimTwoLocalOfLocalFiniteness.lean#L108-L113

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open GlobalTheory GlobalTheory.Published

theorem GlobalTheory.Published.cohDimTwoLocal_of_localFiniteness (h : LocalFiniteness) : CohDimTwoLocal := by sorry
