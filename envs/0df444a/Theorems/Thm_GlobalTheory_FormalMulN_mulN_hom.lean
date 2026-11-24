-- Prove2me | Theorems.Thm_GlobalTheory_FormalMulN_mulN_hom
-- name    : GlobalTheory.FormalMulN.mulN_hom
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:52.093868+00:00
-- url     : https://prove2.me/theorems/0b651275-8614-4ef8-a312-24d50733e020
-- title:
--   Formal Mul N: mul N hom
-- statement:
--   The Formal Mul N construction uses the mul N hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/FormalGroupLawCompMulNZero.lean#L199-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/FormalGroupLawCompMulNZero.lean#L199-L205

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalMulN
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ} (G : FGLaw R d)

theorem GlobalTheory.FormalMulN.mulN_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (n : ℕ),
    (∀ i, constantCoeff (mulN G n i) = 0) ∧
    comp1 (mulN G n) (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
      G.add (comp1 (mulN G n) (pt R (n := 2) d 0)) (comp1 (mulN G n) (pt R (n := 2) d 1)) ∧
    dLin (mulN G n) = (n : R) • (1 : Matrix (Fin d) (Fin d) R) := by sorry
