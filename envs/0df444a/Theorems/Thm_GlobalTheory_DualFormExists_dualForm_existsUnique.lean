-- Prove2me | Theorems.Thm_GlobalTheory_DualFormExists_dualForm_existsUnique
-- name    : GlobalTheory.DualFormExists.dualForm_existsUnique
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:51:54.480785+00:00
-- url     : https://prove2.me/theorems/a182d92d-12a7-4821-910b-f4dde89dab0c
-- title:
--   Dual Form Exists: dual Form exists Unique
-- statement:
--   The Dual Form Exists construction uses the dual Form exists Unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualFormExistsUnique.lean#L120-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualFormExistsUnique.lean#L120-L137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualFormExistsUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
noncomputable section
open GlobalTheory GlobalTheory.DualFormExists

theorem GlobalTheory.DualFormExists.dualForm_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ξ : E), ξ ≠ 0 →
    ∃! B : LinearMap.BilinForm ℂ (Coh E), IsDualForm ξ B := by sorry
