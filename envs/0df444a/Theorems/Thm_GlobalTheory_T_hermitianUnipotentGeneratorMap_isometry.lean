-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitianUnipotentGeneratorMap_isometry
-- name    : GlobalTheory.T.hermitianUnipotentGeneratorMap_isometry
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:39.670421+00:00
-- url     : https://prove2.me/theorems/3543f578-aca5-4eb6-b976-65e04921a049
-- title:
--   T: hermitian Unipotent Generator Map isometry
-- statement:
--   The T construction uses the hermitian Unipotent Generator Map isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianUnipotentGeneratorMapIsometryStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianUnipotentGeneratorMapIsometryStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianUnipotentGeneratorMapIsometry
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianUnipotentGeneratorMapIsometryStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermitianUnipotentGeneratorMap_isometry : ∀ {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K), (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (ρ a) (e b) = 0) → (∀ a b, star (c a b) + c b a + H.B (ρ a) (ρ b) = 0) → ∀ u v : V, H.B (GlobalTheory.RowStab.gen H J e ρ c u) (GlobalTheory.RowStab.gen H J e ρ c v) = H.B u v := by sorry
