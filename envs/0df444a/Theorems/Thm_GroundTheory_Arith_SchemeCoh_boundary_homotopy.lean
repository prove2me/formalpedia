-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_boundary_homotopy
-- name    : GroundTheory.Arith.SchemeCoh.boundary_homotopy
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:02.189725+00:00
-- url     : https://prove2.me/theorems/f0d7d9a3-4573-4b28-9103-566277c5bb69
-- title:
--   Scheme Coh: boundary homotopy
-- statement:
--   The Scheme Coh construction uses the boundary homotopy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L375-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L375-L403

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory
universe w
variable {ι : Type w}
variable [LinearOrder ι]

theorem GroundTheory.Arith.SchemeCoh.boundary_homotopy : ∀ (n : ℕ) (i : Fin (n + 2) → ι),
    bd (n + 1) (hmt (n + 1) i) + lin (hmt n) (bd n (Finsupp.single i 1)) =
      Finsupp.single i 1 - rho (n + 1) i
  := by sorry
