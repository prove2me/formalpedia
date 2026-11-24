-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_idealSheaf_map_comap
-- name    : GlobalTheory.GaloisDescent.idealSheaf_map_comap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:43:25.464314+00:00
-- url     : https://prove2.me/theorems/87eb2b22-9fc0-4804-aff5-28bb017cb925
-- title:
--   Galois Descent: ideal Sheaf map comap
-- statement:
--   The Galois Descent construction uses the ideal Sheaf map comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueComapEqVanishingIdeal.lean#L92-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueComapEqVanishingIdeal.lean#L92-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace GlobalTheory.QCoh.Qcqs
universe u
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L : Type u} [Field K] [Field L] [Algebra K L] {X Y : Scheme.{u}}
  {p : X ⟶ Spec (.of K)} {q : Y ⟶ Spec (.of L)} {π : Y ⟶ X}
  (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap K L)))) {G : Type*}
include H

theorem GlobalTheory.GaloisDescent.idealSheaf_map_comap (J : X.IdealSheafData) : (J.comap π).map π = J := by sorry
