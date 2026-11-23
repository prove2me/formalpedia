-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_exists_primRoot_pow
-- name    : GlobalTheory.Cyc.exists_primRoot_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:45.959792+00:00
-- url     : https://prove2.me/theorems/164f1f89-96df-4eca-89cc-cd921ada96ce
-- title:
--   Cyc: exists prim Root pow
-- statement:
--   The Cyc construction uses the exists prim Root pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicProperties.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicProperties.lean#L11-L14

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

theorem GlobalTheory.Cyc.exists_primRoot_pow (m : ℕ) : ∃ ζ : Om l, IsPrimitiveRoot ζ (l ^ m) := by sorry
