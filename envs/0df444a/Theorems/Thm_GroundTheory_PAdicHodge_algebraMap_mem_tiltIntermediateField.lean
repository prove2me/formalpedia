-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_algebraMap_mem_tiltIntermediateField
-- name    : GroundTheory.PAdicHodge.algebraMap_mem_tiltIntermediateField
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:59.742153+00:00
-- url     : https://prove2.me/theorems/924f154d-7dc6-4e57-a969-bafffade6e77
-- title:
--   PAdic Hodge: algebra Map mem tilt Intermediate Field
-- statement:
--   The PAdic Hodge construction uses the algebra Map mem tilt Intermediate Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltAlgebra.lean#L204-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltAlgebra.lean#L204-L222

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
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
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
variable (F : IntermediateField K C) [IsPerfectoidField F p]
local notation "F♭" => Tilt F NormedField.valuation (normInteger F) normInteger_integers p

theorem GroundTheory.PAdicHodge.algebraMap_mem_tiltIntermediateField {a : 𝒪C♭}
    (ha : ∀ n, ((PreTilt.untilt ((frobeniusEquiv 𝒪C♭ p).symm^[n] a) : normInteger C) : C) ∈ F) :
    algebraMap 𝒪C♭ C♭ a ∈ tiltIntermediateField p F := by sorry
