-- Prove2me | Theorems.Thm_GlobalTheory_JR_OrbitProper_conj_pow_GL
-- name    : GlobalTheory.JR.OrbitProper.conj_pow_GL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:54.281478+00:00
-- url     : https://prove2.me/theorems/1f12fe7b-0773-4af6-826f-90086cdeffe9
-- title:
--   Orbit Proper: conj pow GL
-- statement:
--   The Orbit Proper construction uses the conj pow GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisOrbitInvariantMapProper.lean#L23-L26

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbitProper
variable {r : ℕ} {k : Type} [CommRing k]

theorem GlobalTheory.JR.OrbitProper.conj_pow_GL (g : GL (Fin r) k) (A : Matrix (Fin r) (Fin r) k) (j : ℕ) :
    ((g : Matrix (Fin r) (Fin r) k) * A * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)) ^ j =
      (g : Matrix (Fin r) (Fin r) k) * A ^ j * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by sorry
