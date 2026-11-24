-- Prove2me | Theorems.Thm_GlobalTheory_exists_algHom_ker_eq_of_isMaximal
-- name    : GlobalTheory.exists_algHom_ker_eq_of_isMaximal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:29:01.554538+00:00
-- url     : https://prove2.me/theorems/f3b62fe9-8cdf-4201-9d33-97d6f3fe812d
-- title:
--   Global Theory: exists alg Hom ker eq of is Maximal
-- statement:
--   The Global Theory construction uses the exists alg Hom ker eq of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/TensorEqZeroOfForallGeometricPoint.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/TensorEqZeroOfForallGeometricPoint.lean#L7-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorEqZeroOfForallGeometricPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory

theorem GlobalTheory.exists_algHom_ker_eq_of_isMaximal (F B : Type) [Field F] [IsAlgClosed F] [CommRing B]
    [Algebra F B] [Module.Finite F B] (m : Ideal B) [m.IsMaximal] :
    ∃ ψ : B →ₐ[F] F, ∀ b, ψ b = 0 → b ∈ m := by sorry
