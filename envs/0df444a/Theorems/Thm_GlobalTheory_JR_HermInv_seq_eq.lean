-- Prove2me | Theorems.Thm_GlobalTheory_JR_HermInv_seq_eq
-- name    : GlobalTheory.JR.HermInv.seq_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:33:02.766324+00:00
-- url     : https://prove2.me/theorems/6d84f47e-96d1-4cb1-bd2d-981910e46f55
-- title:
--   Herm Inv: seq eq
-- statement:
--   The Herm Inv construction uses the seq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L82-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActionHermitianInvariantsTransitive.lean#L82-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ} {K : Type} [CommRing K]

theorem GlobalTheory.JR.HermInv.seq_eq {u v : ℕ → K} (q : Fin r → K) (hu : ∀ k, u (k + r) = -((fun j : Fin r => u (k + j)) ⬝ᵥ q))
    (hv : ∀ k, v (k + r) = -((fun j : Fin r => v (k + j)) ⬝ᵥ q)) (h : ∀ k < r, u k = v k) : u = v := by sorry
