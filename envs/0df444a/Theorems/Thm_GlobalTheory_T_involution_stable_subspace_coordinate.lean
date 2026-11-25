-- Prove2me | Theorems.Thm_GlobalTheory_T_involution_stable_subspace_coordinate
-- name    : GlobalTheory.T.involution_stable_subspace_coordinate
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:40:20.972898+00:00
-- url     : https://prove2.me/theorems/c0898e2c-8605-4c93-9c92-650e5bf96817
-- title:
--   T: involution stable subspace coordinate
-- statement:
--   The T construction uses the involution stable subspace coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsOrthogonalHermitianSubspaceStatement.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExistsOrthogonalHermitianSubspaceStatement.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsOrthogonalHermitianSubspace
import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExistsOrthogonalHermitianSubspaceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.involution_stable_subspace_coordinate : ∀ {n : ℕ} (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), (∀ v ∈ W, Formalism.REAL.Jm ε *ᵥ v ∈ W) →
    ∃ (k : Formalism.REAL.KG ε) (S : Set (Fin n)),
      W = (Submodule.span ℂ (Set.range fun j : S => (Pi.single (j : Fin n) (1 : ℂ) : Fin n → ℂ))).map (Formalism.REAL.toMK k).mulVecLin := by sorry
