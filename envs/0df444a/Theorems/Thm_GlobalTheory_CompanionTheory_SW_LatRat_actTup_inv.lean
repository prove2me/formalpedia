-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatRat_actTup_inv
-- name    : GlobalTheory.CompanionTheory.SW.LatRat.actTup_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:06:32.533082+00:00
-- url     : https://prove2.me/theorems/297be0e3-b7b4-477f-8293-577dcd8de95b
-- title:
--   Lat Rat: act Tup inv
-- statement:
--   The Lat Rat construction uses the act Tup inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeStableAlmostEverywhere.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeStableAlmostEverywhere.lean#L96-L101

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatRat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
omit [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.LatRat.actTup_inv {M n : ℕ} (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    actTup R (bc (inclR R) g⁻¹) (actTup R (bc (inclR R) g) X) = X := by sorry
