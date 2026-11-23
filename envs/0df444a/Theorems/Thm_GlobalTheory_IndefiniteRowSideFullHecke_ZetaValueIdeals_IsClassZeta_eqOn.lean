-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ZetaValueIdeals_IsClassZeta_eqOn
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.IsClassZeta.eqOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:25.730484+00:00
-- url     : https://prove2.me/theorems/2ed931d5-5faf-4afe-b8f1-47dcf0960b8f
-- title:
--   Is Class Zeta: eq On
-- statement:
--   The Is Class Zeta construction uses the eq On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/ZetaValueIdeals.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/ZetaValueIdeals.lean#L54-L62

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ZetaValueIdeals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.IsClassZeta.eqOn {C : ClassGroup (𝓞 F)} {Z Z' : ℂ → ℂ} (h : IsClassZeta C Z) (h' : IsClassZeta C Z') :
    Set.EqOn Z Z' {1}ᶜ := by sorry
