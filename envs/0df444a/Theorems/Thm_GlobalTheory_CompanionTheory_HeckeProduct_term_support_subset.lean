-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_term_support_subset
-- name    : GlobalTheory.CompanionTheory.HeckeProduct.term_support_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:45.13018+00:00
-- url     : https://prove2.me/theorems/b32375fe-8206-4c50-bc2c-a2bc6fc5f300
-- title:
--   Hecke Product: term support subset
-- statement:
--   The Hecke Product construction uses the term support subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportConvolutionTriple.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportConvolutionTriple.lean#L21-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportConvolutionTriple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeProduct
variable {G M V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ G V) (K : Subgroup G) {f : G → ℂ}

theorem GlobalTheory.CompanionTheory.HeckeProduct.term_support_subset (hf : (Function.support fun q : G ⧸ K => f q.out).Finite) (u : V) :
    (Function.support fun q : G ⧸ K => f q.out • π q.out u) ⊆ hf.toFinset := by sorry
