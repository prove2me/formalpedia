-- Prove2me | Theorems.Thm_GroundTheory_Global_integerUnitsAddEquiv_decomposition
-- name    : GroundTheory.Global.integerUnitsAddEquiv_decomposition
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:05:40.299807+00:00
-- url     : https://prove2.me/theorems/c7107705-e9d5-5270-b479-0588abdc038f
-- title:
--   Global: integer Units Add Equiv decomposition
-- statement:
--   The Global construction uses the integer Units Add Equiv decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L223-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrand.lean#L223-L236

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
variable [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

theorem GroundTheory.Global.integerUnitsAddEquiv_decomposition (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : Additive (w.adicCompletionIntegers L)ˣ) :
    integerUnitsAddEquiv w (Representation.ofMulDistribMulAction
        (MulAction.stabilizer Gal(L/K) w.asIdeal) (w.adicCompletionIntegers L)ˣ σ x) =
      Representation.ofMulDistribMulAction Gal(w.adicCompletion L/v.adicCompletion K)
        𝒪[w.adicCompletion L]ˣ (decompositionMulEquiv v w σ) (integerUnitsAddEquiv w x) := by sorry
