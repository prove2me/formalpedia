-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_smodEq_pow_iff
-- name    : GroundTheory.PAdicHodge.AInf.smodEq_pow_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:23.821808+00:00
-- url     : https://prove2.me/theorems/3b7345bd-e8a7-41db-8178-9744e2ee7dcf
-- title:
--   AInf: smod Eq pow iff
-- statement:
--   The AInf construction uses the smod Eq pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L264-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L264-L266

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
omit hp [IsPerfectoidField K p]

theorem GroundTheory.PAdicHodge.AInf.smodEq_pow_iff {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule A A)] ↔ x - y ∈ I ^ n := by sorry
