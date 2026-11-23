-- Prove2me | Theorems.Thm_GlobalTheory_IsAdicFamily_closedPoint_eq
-- name    : GlobalTheory.IsAdicFamily.closedPoint_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:36.655989+00:00
-- url     : https://prove2.me/theorems/1dbfbbf4-1817-4ab6-891d-5da48a72247e
-- title:
--   Is Adic Family: closed Point eq
-- statement:
--   The Is Adic Family construction uses the closed Point eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L256-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L256-L263

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}
variable [IsLocalRing R]

theorem GlobalTheory.IsAdicFamily.closedPoint_eq (hI : I ≠ ⊤) {X : Scheme.{u}}
    {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X} (hf : IsAdicFamily I f) (n : ℕ) :
    haveI := isLocalRing_quotient_pow hI n
    haveI := isLocalRing_quotient_pow hI 0
    f n (closedPoint (R ⧸ I ^ (n + 1))) = f 0 (closedPoint (R ⧸ I ^ (0 + 1))) := by sorry
