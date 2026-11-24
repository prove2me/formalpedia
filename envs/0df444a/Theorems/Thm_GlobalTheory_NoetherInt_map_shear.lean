-- Prove2me | Theorems.Thm_GlobalTheory_NoetherInt_map_shear
-- name    : GlobalTheory.NoetherInt.map_shear
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:34:26.664902+00:00
-- url     : https://prove2.me/theorems/3ad866a2-7c1c-463e-b7bc-a7d8bec3d706
-- title:
--   Noether Int: map shear
-- statement:
--   The Noether Int construction uses the map shear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L103-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open MvPolynomial
variable {A : Type*} [CommRing A] {n : ℕ}

theorem GlobalTheory.NoetherInt.map_shear {B : Type*} [CommRing B] (φ : A →+* B) (u : ℕ)
    (g : MvPolynomial (Fin (n + 1)) A) :
    MvPolynomial.map φ (shear A n u g) = shear B n u (MvPolynomial.map φ g) := by sorry
