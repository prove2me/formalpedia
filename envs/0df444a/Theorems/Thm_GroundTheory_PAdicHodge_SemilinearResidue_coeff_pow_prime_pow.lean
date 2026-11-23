-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_coeff_pow_prime_pow
-- name    : GroundTheory.PAdicHodge.SemilinearResidue.coeff_pow_prime_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:56.173072+00:00
-- url     : https://prove2.me/theorems/c37ee05c-19aa-4a19-9701-d919dfa667e6
-- title:
--   Semilinear Residue: coeff pow prime pow
-- statement:
--   The Semilinear Residue construction uses the coeff pow prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean#L16-L20

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Module Finset
open GroundTheory.PAdicHodge.SemilinearResidue
variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
include hp

theorem GroundTheory.PAdicHodge.SemilinearResidue.coeff_pow_prime_pow (f : k[X]) (e n : ℕ) :
    (f ^ p ^ e).coeff n = if p ^ e ∣ n then f.coeff (n / p ^ e) ^ p ^ e else 0 := by sorry
