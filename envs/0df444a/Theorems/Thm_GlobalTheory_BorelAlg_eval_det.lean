-- Prove2me | Theorems.Thm_GlobalTheory_BorelAlg_eval_det
-- name    : GlobalTheory.BorelAlg.eval_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:44.516982+00:00
-- url     : https://prove2.me/theorems/0199c81b-dfda-4f4f-98e2-749b1e692637
-- title:
--   Borel Alg: eval det
-- statement:
--   The Borel Alg construction uses the eval det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L60-L66

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
variable {ι : Type} (m : ι → ℕ) (L : Type) [Field L]

theorem GlobalTheory.BorelAlg.eval_det {T : Type*} [CommRing T] (c : L →+* T)
    (y : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T) (τ : ι) :
    eval₂Hom c (fun p : Lt m => y p.1 p.2.1 p.2.2) (gen m L τ).det = (y τ).det := by sorry
