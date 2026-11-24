-- Prove2me | Theorems.Thm_GlobalTheory_MulCocycle_finsupp_homotopy
-- name    : GlobalTheory.MulCocycle.finsupp_homotopy
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:29:20.900996+00:00
-- url     : https://prove2.me/theorems/c6d962e8-4fb9-4811-93cd-84bfe8fde5b3
-- title:
--   Mul Cocycle: finsupp homotopy
-- statement:
--   The Mul Cocycle construction uses the finsupp homotopy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUnitCoboundaryOfMulCocycle.lean#L10-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUnitCoboundaryOfMulCocycle.lean#L10-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitCoboundaryOfMulCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.MulCocycle

theorem GlobalTheory.MulCocycle.finsupp_homotopy {X : Type*} [Zero X] {N : Type*} [AddCommGroup N] (f : X × X →₀ N)
    (g : X →₀ N) (hg : ∀ x, g x = f (0, x)) (q : X × X) :
    (f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
        f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) :
          X × X × X →₀ N) (0, q) =
      (f - (g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
        g.mapDomain (fun y => (y, (0 : X)))) : X × X →₀ N) q := by sorry
