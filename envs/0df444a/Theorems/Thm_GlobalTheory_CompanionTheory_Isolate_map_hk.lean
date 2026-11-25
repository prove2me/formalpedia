-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Isolate_map_hk
-- name    : GlobalTheory.CompanionTheory.Isolate.map_hk
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:01:29.902862+00:00
-- url     : https://prove2.me/theorems/cb423ffd-094d-5697-8d01-02ee402d70f9
-- title:
--   Isolate: map hk
-- statement:
--   The Isolate construction uses the map hk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsolateRepresentationAtCharacter.lean#L124-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsolateRepresentationAtCharacter.lean#L124-L135

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HkMemFixed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmulEqOnFinset
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsolateRepresentationAtCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Isolate
open GlobalTheory.CompanionTheory.HeckeMul
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.Isolate.map_hk {K : Subgroup (GL ι F)} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ (GL ι F) V} {σ : Representation ℂ (GL ι F) W}
    (T : ρ.Equiv σ) (e : GL ι F → ℂ) (v : V) :
    T.toLinearEquiv (hk ρ K e v) = hk σ K e (T.toLinearEquiv v) := by sorry
