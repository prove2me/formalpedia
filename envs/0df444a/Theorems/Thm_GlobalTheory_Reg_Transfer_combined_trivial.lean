-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_combined_trivial
-- name    : GlobalTheory.Reg.Transfer.combined_trivial
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:18:36.203958+00:00
-- url     : https://prove2.me/theorems/c0d3d417-6bc6-401d-8611-5973b9a896b6
-- title:
--   Transfer: combined trivial
-- statement:
--   The Transfer construction uses the combined trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentreChart.lean#L141-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentreChart.lean#L141-L210

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
set_option maxHeartbeats 1000000

theorem GlobalTheory.Reg.Transfer.combined_trivial {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (hQ : S.CovQ) {m : ℕ} (ws : Fin m → Rul Xo c) (hF : S.FamW ws)
    {aL nL} (hws : ∀ k, ws k ∈ sec Xo c aL nL)
    {aE nE} {et : Rul Xo c} (het : et ∈ sec Xo c aE nE)
    (nu c' : ℝ) (hc' : 0 ≤ c')
    (hyp : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v et ∧
      (v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu : EReal) + (c' : EReal) * v et)) :
    ∀ q ∈ trivSet Xo c, q et ≠ ⊤ → (⨅ k, q (ws k)) ≤ (c' : EReal) * q et := by sorry
