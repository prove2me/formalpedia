-- Prove2me | Theorems.Thm_GlobalTheory_MultiplicativeSeries_partial_eq
-- name    : GlobalTheory.MultiplicativeSeries.partial_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:29:32.661365+00:00
-- url     : https://prove2.me/theorems/753e00b0-4e76-43af-a489-fe82430664d9
-- title:
--   Multiplicative Series: partial eq
-- statement:
--   The Multiplicative Series construction uses the partial eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvSelfTwo.lean#L46-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvSelfTwo.lean#L46-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvSelfTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.MultiplicativeSeries
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ}

theorem GlobalTheory.MultiplicativeSeries.partial_eq (G : FGLaw R d) (s : PS R 1 d)
    (h : ev (n := 2) ![G.add (pt R d 0) (pt R d 1)] s =
      ev (n := 2) ![pt R d 0] s * ev (n := 2) ![pt R d 1] s) (i : Fin d) :
    ∑ j, ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F j)) *
        pderiv R ((0 : Fin 1), j) s =
      C (coeff (Finsupp.single ((0 : Fin 1), i) 1) s) * s := by sorry
