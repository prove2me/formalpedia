-- Prove2me | Theorems.Thm_GroundTheory_Global_cycHerbrand_adicCompletion_units
-- name    : GroundTheory.Global.cycHerbrand_adicCompletion_units
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:49.090797+00:00
-- url     : https://prove2.me/theorems/1d50f44e-26bd-4a5b-992a-5058a38cab42
-- title:
--   Global: cyc Herbrand adic Completion units
-- statement:
--   The Global construction uses the cyc Herbrand adic Completion units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L170-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L170-L190

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.GroupCoh
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem GroundTheory.Global.cycHerbrand_adicCompletion_units [Fintype (MulAction.stabilizer Gal(L/K) w.asIdeal)]
    (τ : MulAction.stabilizer Gal(L/K) w.asIdeal) (hτ : ∀ σ, σ ∈ Subgroup.zpowers τ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.adicCompletion L)ˣ) τ)
        (cycNorm (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.adicCompletion L)ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.adicCompletion L)ˣ) τ =
        Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by sorry
