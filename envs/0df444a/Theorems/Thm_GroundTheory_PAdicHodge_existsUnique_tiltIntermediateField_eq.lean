-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_existsUnique_tiltIntermediateField_eq
-- name    : GroundTheory.PAdicHodge.existsUnique_tiltIntermediateField_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:09:25.134631+00:00
-- url     : https://prove2.me/theorems/0bfdb8d3-33cb-4910-97b7-5c0ce985daff
-- title:
--   PAdic Hodge: exists Unique tilt Intermediate Field eq
-- statement:
--   The PAdic Hodge construction uses the exists Unique tilt Intermediate Field eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltEquiv.lean#L96-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltEquiv.lean#L96-L105

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApprox
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
import Definitions.Def_GroundTheory_PAdicHodge_CompletedAlgClosure
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCharP
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgClosed
import Definitions.Def_GroundTheory_PAdicHodge_TiltEquiv
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
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C] [IsAlgClosed C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
variable [IsPerfectoidField C p]

theorem GroundTheory.PAdicHodge.existsUnique_tiltIntermediateField_eq (M : IntermediateField K♭ C♭)
    [FiniteDimensional K♭ M] :
    ∃! L : IntermediateField K C, ∃ _ : FiniteDimensional K L, tiltIntermediateField p L = M := by sorry
