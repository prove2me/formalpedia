-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FlagSectionAction_coef_mem_flagSec
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction.coef_mem_flagSec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:44:59.313855+00:00
-- url     : https://prove2.me/theorems/db96f797-3463-4ece-8aa4-1c587acafed7
-- title:
--   Flag Section Action: coef mem flag Sec
-- statement:
--   The Flag Section Action construction uses the coef mem flag Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/CoefMemFlagSec.lean#L72-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/CoefMemFlagSec.lean#L72-L82

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.FlagSectionAction.coef_mem_flagSec {K : Type} [Field K] (σ : K →+* ℂ) (X : Data E r) (la : Wt X.Ψ r) (cu : FJ.CuspFD X ρ)
    (hd : ∀ t, ∀ x ∈ X.dom, zAct X cu t x ∈ X.dom) (ph : Fin (nZ X ρ) → ℝ) (P : OrbInt (zAct X cu) X.dom)
    (hP : IsFlagSec X la P) :
    (show FnVia σ (Frame X.Ψ r) from coefL (zAct X cu) X.dom ph P) ∈ flagSec σ X la := by sorry
