-- Prove2me | Theorems.Thm_GlobalTheory_SplitComp_exists_imag
-- name    : GlobalTheory.SplitComp.exists_imag
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:20:02.836146+00:00
-- url     : https://prove2.me/theorems/18bdb319-8fa3-4b20-929e-5a2dfbae7de6
-- title:
--   Split Comp: exists imag
-- statement:
--   The Split Comp construction uses the exists imag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRealAdd.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsRealAdd.lean#L10-L17

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRealAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 TensorProduct
open GlobalTheory GlobalTheory.SplitComp
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

theorem GlobalTheory.SplitComp.exists_imag : ∃ θ : L, θ ≠ 0 ∧ IsCMField.complexConj L θ = -θ := by sorry
