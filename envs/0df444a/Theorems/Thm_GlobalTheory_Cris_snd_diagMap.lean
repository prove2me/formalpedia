-- Prove2me | Theorems.Thm_GlobalTheory_Cris_snd_diagMap
-- name    : GlobalTheory.Cris.snd_diagMap
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:19.61213+00:00
-- url     : https://prove2.me/theorems/f831aff5-edff-464c-9992-0c9c1d62e0d0
-- title:
--   Cris: snd diag Map
-- statement:
--   The Cris construction uses the snd diag Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CrystallineConnectionFormCoboundaryZero.lean#L80-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CrystallineConnectionFormCoboundaryZero.lean#L80-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
open KaehlerDifferential
variable (R) (B B' : Type) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
attribute [local instance] opModule
attribute [local instance] isCentralScalar_kaehler isScalarTower_kaehler
variable {B B'}

theorem GlobalTheory.Cris.snd_diagMap [Algebra B B'] [IsScalarTower R B B'] (c : TrivSqZeroExt B Ω[B⁄R]) :
    (diagMap R B B' c).snd = KaehlerDifferential.map R R B B' c.snd := by sorry
