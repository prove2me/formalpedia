-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Isolate_exists_hk_avg
-- name    : GlobalTheory.CompanionTheory.Isolate.exists_hk_avg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:27.571258+00:00
-- url     : https://prove2.me/theorems/a1387971-cddb-4eff-a346-f4338aafe174
-- title:
--   Isolate: exists hk avg
-- statement:
--   The Isolate construction uses the exists hk avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsolateRepresentationAtCharacter.lean#L153-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsolateRepresentationAtCharacter.lean#L153-L237

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

theorem GlobalTheory.CompanionTheory.Isolate.exists_hk_avg {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F)))
    (hKc : IsCompact (K : Set (GL ι F))) (L : Subgroup K) [Fintype (K ⧸ L)] (g : GL ι F)
    (hL : ∀ l ∈ L, g⁻¹ * ((l : K) : GL ι F) * g ∈ K)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V) {s : V}
    (hs : s ∈ fixed ρ K) :
    ∃ e, IsHk K e ∧ hk ρ K e s = ∑ q : K ⧸ L, ρ ((q.out : K) : GL ι F) (ρ g s) := by sorry
