-- Prove2me | Theorems.Thm_GroundTheory_Global_hasDirichletDensity_inter_degreeOnePrimes_iff
-- name    : GroundTheory.Global.hasDirichletDensity_inter_degreeOnePrimes_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:15:51.50703+00:00
-- url     : https://prove2.me/theorems/ee6bf454-9232-49ac-9efe-224efac47e85
-- title:
--   Global: has Dirichlet Density inter degree One Primes iff
-- statement:
--   The Global construction uses the has Dirichlet Density inter degree One Primes iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L93-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L93-L102

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
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
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (K)

theorem GroundTheory.Global.hasDirichletDensity_inter_degreeOnePrimes_iff (S : Set (HeightOneSpectrum (𝓞 L)))
    (δ : ℝ) : (S ∩ degreeOnePrimes K L).HasDirichletDensity δ ↔ S.HasDirichletDensity δ := by sorry
