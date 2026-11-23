-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_map_heckeSum
-- name    : GlobalTheory.CompanionTheory.HeckeProduct.map_heckeSum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:42.845526+00:00
-- url     : https://prove2.me/theorems/d9fa5eb1-a1d3-42bc-840b-60ee707e9a61
-- title:
--   Hecke Product: map hecke Sum
-- statement:
--   The Hecke Product construction uses the map hecke Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportConvolutionTriple.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportConvolutionTriple.lean#L32-L36

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

theorem GlobalTheory.CompanionTheory.HeckeProduct.map_heckeSum (hf : (Function.support fun q : G ⧸ K => f q.out).Finite)
    (T : V →ₗ[ℂ] V) (hT : ∀ g u, T (π g u) = π g (T u)) (u : V) :
    T (heckeSum π K f u) = heckeSum π K f (T u) := by sorry
