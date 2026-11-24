-- Prove2me | Theorems.Thm_GlobalTheory_splitPlace_proj_mem_integers_of_integral
-- name    : GlobalTheory.splitPlace_proj_mem_integers_of_integral
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:21.817562+00:00
-- url     : https://prove2.me/theorems/a4ab0831-febb-4b8c-adae-5302e429ca30
-- title:
--   Global Theory: split Place proj mem integers of integral
-- statement:
--   The Global Theory construction uses the split Place proj mem integers of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SplitPlaceProjMemIntegersOfIntegral.lean#L10-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SplitPlaceProjMemIntegersOfIntegral.lean#L10-L29

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SplitPlaceProjMemIntegersOfIntegral
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
open NumberField IsDedekindDomain

theorem GlobalTheory.splitPlace_proj_mem_integers_of_integral {L : Type} [Field L] [NumberField L] [IsCMField L]
    (s : _root_.ReciprocityTheory.Aut.SplitPlace L) {y : _root_.ReciprocityTheory.Aut.AL L} (hy : y ∈ _root_.ReciprocityTheory.Aut.ALint L) :
    s.proj y ∈ s.v.adicCompletionIntegers (NumberField.maximalRealSubfield L) := by sorry
