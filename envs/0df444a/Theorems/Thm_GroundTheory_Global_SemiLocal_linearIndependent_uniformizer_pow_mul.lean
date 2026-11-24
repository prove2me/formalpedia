-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_linearIndependent_uniformizer_pow_mul
-- name    : GroundTheory.Global.SemiLocal.linearIndependent_uniformizer_pow_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:28.527553+00:00
-- url     : https://prove2.me/theorems/1e0035b7-af8b-4792-959b-ebd3355db21c
-- title:
--   Semi Local: linear Independent uniformizer pow mul
-- statement:
--   The Semi Local construction uses the linear Independent uniformizer pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L193-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L193-L260

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
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
open IsDedekindDomain NumberField WithZero
noncomputable section
open GroundTheory.Global.SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]
variable {ι : Type*} [Fintype ι]
omit [Fintype ι]

theorem GroundTheory.Global.SemiLocal.linearIndependent_uniformizer_pow_mul [Finite ι] (ω : ι → 𝓞 L)
    (hω : LinearIndependent (𝓞 K ⧸ v.asIdeal) (fun j ↦ Ideal.Quotient.mk w.asIdeal (ω j)))
    (π : L) (hπ : w.valuation L π = exp (-1 : ℤ)) :
    LinearIndependent (v.adicCompletion K)
      (fun p : Fin (w.asIdeal.ramificationIdx (𝓞 K)) × ι ↦
        algebraMap L (w.adicCompletion L) π ^ (p.1 : ℕ) *
          algebraMap (𝓞 L) (w.adicCompletion L) (ω p.2)) := by sorry
