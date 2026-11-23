-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_IsCyc_norm_sub_one_le_of_prim
-- name    : GlobalTheory.Cyc.IsCyc.norm_sub_one_le_of_prim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:15.33785+00:00
-- url     : https://prove2.me/theorems/8b121166-a5bb-4227-b3a4-91eda94cf121
-- title:
--   Is Cyc: norm sub one le of prim
-- statement:
--   The Is Cyc construction uses the norm sub one le of prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicProperties.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicProperties.lean#L28-L38

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.IsCyc.norm_sub_one_le_of_prim {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) (m : ℕ)
    {ζ : Om l} (hζ : IsPrimitiveRoot ζ (l ^ m)) (hg : g ζ = ζ) :
    ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by sorry
