-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_vr_of_over
-- name    : GlobalTheory.Reg.Transfer.vr_of_over
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:24.204796+00:00
-- url     : https://prove2.me/theorems/fdb81e29-8fbc-4f04-8afe-be5b77a103d4
-- title:
--   Transfer: vr of over
-- statement:
--   The Transfer construction uses the vr of over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentreChart.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentreChart.lean#L60-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentreChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing NumberField IsDedekindDomain Formalism.L2.Pj Formalism.L2.PjFree ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Reg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem GlobalTheory.Reg.Transfer.vr_of_over {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (eO e : ℕ) (heO : 0 < eO)
    (he : 0 < e) (y : V) (hy : vV (K' := FractionRing V) V (algebraMap V (FractionRing V) y) * (eO : ℤ) = e) :
    vr e y = 1 / eO := by sorry
