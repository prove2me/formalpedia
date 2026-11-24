-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_frobeniusEquiv_symm_pow_apply_pow
-- name    : GroundTheory.PAdicHodge.frobeniusEquiv_symm_pow_apply_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:21.546677+00:00
-- url     : https://prove2.me/theorems/b936108c-dadf-40e1-a3bd-a4c3237352b4
-- title:
--   PAdic Hodge: frobenius Equiv symm pow apply pow
-- statement:
--   The PAdic Hodge construction uses the frobenius Equiv symm pow apply pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L128-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L128-L134

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
variable [CharP R p]
variable [PerfectRing R p]

theorem GroundTheory.PAdicHodge.frobeniusEquiv_symm_pow_apply_pow (y : R) (n : ℕ) :
    ((_root_.frobeniusEquiv R p).symm ^ n) y ^ p ^ n = y := by sorry
