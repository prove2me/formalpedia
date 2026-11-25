-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_cosets_heckeSet_at_splitPlace_outside_level
-- name    : GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:39.307849+00:00
-- url     : https://prove2.me/theorems/2049dea5-a065-4ebe-a025-dbb74edc6012
-- title:
--   T: finite cosets hecke Set at split Place outside level
-- statement:
--   The T construction uses the finite cosets hecke Set at split Place outside level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FiniteCosetsHeckeSetAtSplitPlaceOutsideLevelStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FiniteCosetsHeckeSetAtSplitPlaceOutsideLevelStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FiniteCosetsHeckeSetAtSplitPlaceOutsideLevelStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (Formalism.AUTREP.GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), Formalism.L2.NG.HypOutside J χ B → ∀ (s : ReciprocityTheory.Aut.SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → Formalism.AUTREP.IsUnif L s.v ϖ → ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Formalism.AUTREP.tSet L n s ϖ k).Finite := by sorry
