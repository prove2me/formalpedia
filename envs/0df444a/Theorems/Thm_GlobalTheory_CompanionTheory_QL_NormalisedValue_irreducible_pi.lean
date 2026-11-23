-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_irreducible_pi
-- name    : GlobalTheory.CompanionTheory.QL.NormalisedValue.irreducible_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:26.531678+00:00
-- url     : https://prove2.me/theorems/06b0a769-5fdc-4b21-8768-4fcb68106cc5
-- title:
--   Normalised Value: irreducible pi
-- statement:
--   The Normalised Value construction uses the irreducible pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldUniformizerNormProperties.lean#L41-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldUniformizerNormProperties.lean#L41-L64

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.NormalisedValue
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem GlobalTheory.CompanionTheory.QL.NormalisedValue.irreducible_pi (h : LF O ϖ nrm q) :
    Irreducible (⟨ϖ, (Valuation.mem_integer_iff _ _).2 (val_pi_lt_one h).le⟩ : 𝒪[F]) := by sorry
