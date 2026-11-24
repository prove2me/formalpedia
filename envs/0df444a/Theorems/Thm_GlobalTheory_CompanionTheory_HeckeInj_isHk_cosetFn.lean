-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_isHk_cosetFn
-- name    : GlobalTheory.CompanionTheory.HeckeInj.isHk_cosetFn
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:46:39.526653+00:00
-- url     : https://prove2.me/theorems/52b65646-b953-4c85-8f72-039879a6f067
-- title:
--   Hecke Inj: is Hk coset Fn
-- statement:
--   The Hecke Inj construction uses the is Hk coset Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L100-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L100-L117

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeInj
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.HeckeInj.isHk_cosetFn {K L : Subgroup (GL ι F)} [Fintype (K ⧸ L.subgroupOf K)]
    (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F))) (g : GL ι F)
    (hL : ∀ l ∈ L, g⁻¹ * l * g ∈ K) : IsHk K (cosetFn K L g) := by sorry
