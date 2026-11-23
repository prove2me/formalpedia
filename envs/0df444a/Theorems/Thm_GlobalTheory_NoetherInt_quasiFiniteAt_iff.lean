-- Prove2me | Theorems.Thm_GlobalTheory_NoetherInt_quasiFiniteAt_iff
-- name    : GlobalTheory.NoetherInt.quasiFiniteAt_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:44.828077+00:00
-- url     : https://prove2.me/theorems/d937b15b-2893-43ec-9b03-0f6718a651a3
-- title:
--   Noether Int: quasi Finite At iff
-- statement:
--   The Noether Int construction uses the quasi Finite At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L287-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L287-L293

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

theorem GlobalTheory.NoetherInt.quasiFiniteAt_iff {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (q : Ideal S)
    [q.IsPrime] :
    f.QuasiFiniteAt q ↔ ((algebraMap S (Localization.AtPrime q)).comp f).QuasiFinite := by sorry
