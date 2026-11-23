-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_finite_quotient
-- name    : GroundTheory.Global.Cyclotomic.finite_quotient
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:42.856254+00:00
-- url     : https://prove2.me/theorems/08785a60-5bef-431d-9808-1141c3adf5da
-- title:
--   Cyclotomic: finite quotient
-- statement:
--   The Cyclotomic construction uses the finite quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/Frobenius.lean#L26-L28

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Frobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
variable {m : ℕ} [NeZero m] (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {m} ℚ K]
variable (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
omit [P.IsPrime]
include hp

theorem GroundTheory.Global.Cyclotomic.finite_quotient : Finite (𝓞 K ⧸ P) := by sorry
