-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLeast_nabValN_algebraMap
-- name    : GlobalTheory.ThetaLeast.nabValN_algebraMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:09.496978+00:00
-- url     : https://prove2.me/theorems/0e5cf294-66bc-4fd7-be67-86848442ef39
-- title:
--   Theta Least: nab Val N algebra Map
-- statement:
--   The Theta Least construction uses the nab Val N algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCombinationIntegers.lean#L16-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCombinationIntegers.lean#L16-L60

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCombinationOfMemHaO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_VVAlgebraMapNonnegDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCombinationIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.ThetaLeast
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.QuadDeriv GlobalTheory.GaugeBaseChange

theorem GlobalTheory.ThetaLeast.nabValN_algebraMap (S S' : Type) [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] [Algebra S S']
    (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB S d O) (h : PS S 2 d)
    (hc : MvPowerSeries.constantCoeff h = 0) (w0 : O) (m n : ℕ) (f : PS S n d) (κ : Type) [Fintype κ]
    (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S) :
    nabValN B S' (MvPowerSeries.map (algebraMap S S') h) w0 m (MvPowerSeries.map (algebraMap S S') f) cp
      (fun l j => algebraMap S S' (u l j)) (MvPolynomial.map (algebraMap S S') P) =
      algebraMap S S' (nabValN B S h w0 m f cp u P) := by sorry
