-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_untiltAutHom_bijective
-- name    : GroundTheory.PAdicHodge.untiltAutHom_bijective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:52.697911+00:00
-- url     : https://prove2.me/theorems/d03a4562-0cdd-45bf-8ed2-2172f2e1ea27
-- title:
--   PAdic Hodge: untilt Aut Hom bijective
-- statement:
--   The PAdic Hodge construction uses the untilt Aut Hom bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L81-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltGaloisCorr.lean#L81-L97

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
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
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem GroundTheory.PAdicHodge.untiltAutHom_bijective (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [IsGalois K♭ N] :
    Function.Bijective (untiltAutHom (K := K) (C := C) (p := p) N) ∧
      IsGalois K (untiltField K C p N) := by sorry
