-- Prove2me | Theorems.Thm_GroundTheory_Global_dedekindZetaReal_le_exp
-- name    : GroundTheory.Global.dedekindZetaReal_le_exp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:34.697742+00:00
-- url     : https://prove2.me/theorems/fe8777a6-3c39-48bc-97a0-d0945850902d
-- title:
--   Global: dedekind Zeta Real le exp
-- statement:
--   The Global construction uses the dedekind Zeta Real le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L256-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L256-L262

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem GroundTheory.Global.dedekindZetaReal_le_exp {s : ℝ} (hs : 1 < s) :
    dedekindZetaReal K s ≤
      Real.exp (∑' w : HeightOneSpectrum (𝓞 K),
        ((absNorm w.asIdeal : ℝ) ^ (-s) + 2 * ((absNorm w.asIdeal : ℝ) ^ (-s)) ^ 2)) := by sorry
