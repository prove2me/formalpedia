-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FlagSectionAction_zAct_rmul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction.zAct_rmul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:45:19.500334+00:00
-- url     : https://prove2.me/theorems/5e70e1da-8951-47d0-9f18-e92209c7736a
-- title:
--   Flag Section Action: z Act rmul
-- statement:
--   The Flag Section Action construction uses the z Act rmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/CoefMemFlagSec.lean#L41-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/CoefMemFlagSec.lean#L41-L44

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_CoefMemFlagSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction.zAct_rmul (X : Data E r) (cu : FJ.CuspFD X ρ) (t : Fin (nZ X ρ) → ℝ) (x b : Frame X.Ψ r) :
    zAct X cu t (rmul x b) = rmul (zAct X cu t x) b := by sorry
