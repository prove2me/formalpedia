-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_perLat_stdLat_eq
-- name    : GlobalTheory.RootEx.UnfoldShape.perLat_stdLat_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:54.679871+00:00
-- url     : https://prove2.me/theorems/e854f26b-7078-4290-8416-bddc5ff36b88
-- title:
--   Unfold Shape: per Lat std Lat eq
-- statement:
--   The Unfold Shape construction uses the per Lat std Lat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/VolFreePerLatStdLat.lean#L78-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/VolFreePerLatStdLat.lean#L78-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VolFreePerLatStdLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.RootEx.UnfoldShape.perLat_stdLat_eq {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} {ϖ : 𝒪[k]} (h0 : (ϖ : k) ≠ 0) :
    ((perLat ϖ n' c (stdLat k n) : AddSubgroup _) :
      Set ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k)) =
      Set.univ.pi fun rs : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} =>
        {x | (ϖ : k) ^ boxExp rs.1 * x ∈ 𝒪[k]} := by sorry
