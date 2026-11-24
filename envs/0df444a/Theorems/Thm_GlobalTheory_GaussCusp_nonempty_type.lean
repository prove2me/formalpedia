-- Prove2me | Theorems.Thm_GlobalTheory_GaussCusp_nonempty_type
-- name    : GlobalTheory.GaussCusp.nonempty_type
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:51:16.26895+00:00
-- url     : https://prove2.me/theorems/8457667f-ab9c-4908-8a0c-54fb2fbb5731
-- title:
--   Gauss Cusp: nonempty type
-- statement:
--   The Gauss Cusp construction uses the nonempty type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstRaisingMemEquivariant.lean#L390-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FirstRaisingMemEquivariant.lean#L390-L396

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementHypsConsistent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstRaisingMemEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries (E4)
open GlobalTheory
open GlobalTheory.GaussCusp
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {ζ : E}

theorem GlobalTheory.GaussCusp.nonempty_type (hζ : IsPrimitiveRoot ζ 4) : Nonempty (data hζ).Ψ := by sorry
