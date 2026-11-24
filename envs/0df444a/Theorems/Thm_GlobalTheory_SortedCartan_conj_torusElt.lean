-- Prove2me | Theorems.Thm_GlobalTheory_SortedCartan_conj_torusElt
-- name    : GlobalTheory.SortedCartan.conj_torusElt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:11:56.028069+00:00
-- url     : https://prove2.me/theorems/d3848fad-28a2-4d96-af7b-e79f352a825a
-- title:
--   Sorted Cartan: conj torus Elt
-- statement:
--   The Sorted Cartan construction uses the conj torus Elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CartanAntitone.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CartanAntitone.lean#L35-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_IsCoType
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ValuationDivZpowOrd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CartanAntitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
noncomputable section
open GlobalTheory GlobalTheory.SortedCartan
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SortedCartan.conj_torusElt {N : ℕ} (ϖ : kˣ) (m : Fin N → ℤ) (σ : Equiv.Perm (Fin N)) :
    permUnit σ * torusElt k (Fin N) ϖ m * (permUnit σ)⁻¹ = torusElt k (Fin N) ϖ (m ∘ σ) := by sorry
