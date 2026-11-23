-- Prove2me | Theorems.Thm_GlobalTheory_HeckePoisson_embA_apply
-- name    : GlobalTheory.HeckePoisson.embA_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:31.347105+00:00
-- url     : https://prove2.me/theorems/1dc5ea35-999e-4247-9fba-9c1ef0674965
-- title:
--   Hecke Poisson: emb A apply
-- statement:
--   The Hecke Poisson construction uses the emb A apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EmbAApply.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EmbAApply.lean#L23-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.HeckePoisson
variable {K : Type} [Field K] [NumberField K] {I : Type}

theorem GlobalTheory.HeckePoisson.embA_apply (φ : I → K →+* ℂ) (α : 𝓞 K) (i : I) : embA φ α i = φ i (α : K) := by sorry
