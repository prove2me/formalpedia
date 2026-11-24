-- Prove2me | Theorems.Thm_GlobalTheory_BorelAlg_coeff_scale
-- name    : GlobalTheory.BorelAlg.coeff_scale
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:01:43.200614+00:00
-- url     : https://prove2.me/theorems/b2b72a94-fd41-4843-9e49-86872656a2d4
-- title:
--   Borel Alg: coeff scale
-- statement:
--   The Borel Alg construction uses the coeff scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L9-L24

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

theorem GlobalTheory.BorelAlg.coeff_scale {σ L : Type*} [CommRing L] (Q : MvPolynomial σ L) (n : ℕ) :
    (eval₂Hom ((Polynomial.C : MvPolynomial σ L →+* _).comp C)
      (fun i => Polynomial.X * Polynomial.C (X i)) Q).coeff n = homogeneousComponent n Q := by sorry
