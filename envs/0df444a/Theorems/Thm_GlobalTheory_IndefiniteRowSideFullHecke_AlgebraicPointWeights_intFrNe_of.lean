-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AlgebraicPointWeights_intFrNe_of
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights.intFrNe_of
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:09:10.668295+00:00
-- url     : https://prove2.me/theorems/d0e46fb5-1cb5-4ff7-83ad-67a0ad2822c8
-- title:
--   Algebraic Point Weights: int Fr Ne of
-- statement:
--   The Algebraic Point Weights construction uses the int Fr Ne of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/AlgebraicPointWeights.lean#L62-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/AlgebraicPointWeights.lean#L62-L70

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AlgebraicPointWeights
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights
open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}

theorem GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights.intFrNe_of (h₁ : AlgebraicPointOver Xo c) (h₂ : IntegralFrameAfterExt Xo c) :
    IntFrNe Xo c (fun _ _ y => y.IsAlg) := by sorry
