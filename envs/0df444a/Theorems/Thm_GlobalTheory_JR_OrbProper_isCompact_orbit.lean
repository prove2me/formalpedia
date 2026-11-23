-- Prove2me | Theorems.Thm_GlobalTheory_JR_OrbProper_isCompact_orbit
-- name    : GlobalTheory.JR.OrbProper.isCompact_orbit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:43.505789+00:00
-- url     : https://prove2.me/theorems/deb185df-0635-4b00-9df5-45838b7ad6b6
-- title:
--   Orb Proper: is Compact orbit
-- statement:
--   The Orb Proper construction uses the is Compact orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryOrbitProperOfInvertibleKrylovColumns.lean#L40-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryOrbitProperOfInvertibleKrylovColumns.lean#L40-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitProperOfInvertibleKrylovColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbProper
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem GlobalTheory.JR.OrbProper.isCompact_orbit (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E)
    (h : Inv r F → Matrix (Fin r) (Fin r) E) (hΩ : IsCompact Ω) (hs : ContinuousOn s Ω) (hhc : ContinuousOn h Ω)
    (hb : ∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) (C : Set (Hn r F E)) (hC : IsCompact C) :
    IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := by sorry
