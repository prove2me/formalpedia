-- Prove2me | Theorems.Thm_GlobalTheory_NoetherInt_exists_coeff_map_eq_C
-- name    : GlobalTheory.NoetherInt.exists_coeff_map_eq_C
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:34:55.222712+00:00
-- url     : https://prove2.me/theorems/8e828a5c-607d-4b5b-8fe3-3bbefa594bd4
-- title:
--   Noether Int: exists coeff map eq C
-- statement:
--   The Noether Int construction uses the exists coeff map eq C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L233-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L233-L243

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

theorem GlobalTheory.NoetherInt.exists_coeff_map_eq_C {K : Type*} [Field K] {n : ℕ} (φ : ℤ →+* K)
    (g : MvPolynomial (Fin (n + 1)) ℤ) (hg : MvPolynomial.map φ g ≠ 0) :
    ∃ (u k : ℕ) (a : K), a ≠ 0 ∧
      MvPolynomial.map φ ((finSuccEquiv ℤ n (shear ℤ n u g)).coeff k) = MvPolynomial.C a := by sorry
