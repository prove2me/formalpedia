-- Prove2me | Theorems.Thm_GroundTheory_Global_absNorm_eq_prod_count
-- name    : GroundTheory.Global.absNorm_eq_prod_count
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:05.855728+00:00
-- url     : https://prove2.me/theorems/f9dd9664-5749-4329-9e4e-fc2f8bdbc23c
-- title:
--   Global: abs Norm eq prod count
-- statement:
--   The Global construction uses the abs Norm eq prod count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L116-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L116-L125

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

theorem GroundTheory.Global.absNorm_eq_prod_count {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) (P : Finset (Ideal (𝓞 K)))
    (hP : (UniqueFactorizationMonoid.normalizedFactors I).toFinset ⊆ P) :
    absNorm I = ∏ p ∈ P, absNorm p ^ (UniqueFactorizationMonoid.normalizedFactors I).count p := by sorry
