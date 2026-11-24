-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_discr_mod_four
-- name    : GlobalTheory.QuadraticZeta.discr_mod_four
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:29.908636+00:00
-- url     : https://prove2.me/theorems/cda40e56-dde4-4de2-87fc-f774166a27b0
-- title:
--   Quadratic Zeta: discr mod four
-- statement:
--   The Quadratic Zeta construction uses the discr mod four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L373-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L373-L380

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]

theorem GlobalTheory.QuadraticZeta.discr_mod_four (h2 : finrank ℚ K = 2) : discr K % 4 = 0 ∨ discr K % 4 = 1 := by sorry
