-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_eq_of_supported
-- name    : GroundTheory.Arith.SchemeCoh.eq_of_supported
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:27.973779+00:00
-- url     : https://prove2.me/theorems/a9c79acf-9ebb-4896-a125-6918ea4a132c
-- title:
--   Scheme Coh: eq of supported
-- statement:
--   The Scheme Coh construction uses the eq of supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L78-L82

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

theorem GroundTheory.Arith.SchemeCoh.eq_of_supported {m : ℕ} {M : Type*} [AddCommGroup M] (L L' : Chain ι m →+ M)
    {S : Set (Fin (m + 1) → ι)} (h : ∀ j ∈ S, ∀ z : ℤ, L (Finsupp.single j z) = L' (Finsupp.single j z))
    {c : Chain ι m} (hc : c ∈ Finsupp.supported ℤ ℤ S) : L c = L' c := by sorry
