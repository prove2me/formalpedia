-- Prove2me | Theorems.Thm_GlobalTheory_valued_absNorm_lt_one_adicCompletion
-- name    : GlobalTheory.valued_absNorm_lt_one_adicCompletion
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:24:47.152162+00:00
-- url     : https://prove2.me/theorems/25cd7906-52d3-4a87-846b-66a570cdd204
-- title:
--   Global Theory: valued abs Norm lt one adic Completion
-- statement:
--   The Global Theory construction uses the valued abs Norm lt one adic Completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsNatCongruenceLeOpenSubgroupGL.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsNatCongruenceLeOpenSubgroupGL.lean#L7-L17

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNatCongruenceLeOpenSubgroupGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open GlobalTheory

theorem GlobalTheory.valued_absNorm_lt_one_adicCompletion (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) < 1 := by sorry
