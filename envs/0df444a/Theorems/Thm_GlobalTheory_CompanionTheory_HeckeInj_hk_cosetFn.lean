-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeInj_hk_cosetFn
-- name    : GlobalTheory.CompanionTheory.HeckeInj.hk_cosetFn
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:46:46.583895+00:00
-- url     : https://prove2.me/theorems/b724beab-fd4b-42a0-899a-6642d69d87a8
-- title:
--   Hecke Inj: hk coset Fn
-- statement:
--   The Hecke Inj construction uses the hk coset Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L119-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IrreducibleHomFixedVectors.lean#L119-L147

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

theorem GlobalTheory.CompanionTheory.HeckeInj.hk_cosetFn {K L : Subgroup (GL ι F)} [Fintype (K ⧸ L.subgroupOf K)] (g : GL ι F)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V) {v : V} (hv : v ∈ fixed ρ K) :
    hk ρ K (cosetFn K L g) v = avg ρ K L (ρ g v) := by sorry
