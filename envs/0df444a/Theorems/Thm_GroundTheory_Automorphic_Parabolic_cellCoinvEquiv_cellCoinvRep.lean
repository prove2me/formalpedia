-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellCoinvEquiv_cellCoinvRep
-- name    : GroundTheory.Automorphic.Parabolic.cellCoinvEquiv_cellCoinvRep
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:14.067999+00:00
-- url     : https://prove2.me/theorems/23d5f74c-345b-50fb-b31b-5730f2a1bd45
-- title:
--   Parabolic: cell Coinv Equiv cell Coinv Rep
-- statement:
--   The Parabolic construction uses the cell Coinv Equiv cell Coinv Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCharacters.lean#L279-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCharacters.lean#L279-L286

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

theorem GroundTheory.Automorphic.Parabolic.cellCoinvEquiv_cellCoinvRep (b : cellLeviParabolic F β γ w)
    (x : Representation.Coinvariants (cellRepA β γ w σ)) :
    cellCoinvEquiv β γ w σ (cellCoinvRep σ b x) =
      sqrtModular F n β (permConj F β w (Subgroup.inclusion cellLeviParabolic_le_blockUpper b)) •
        levJacquetAction β σ (γ ∘ ⇑w⁻¹) (cellInnerHom β γ w b) (cellCoinvEquiv β γ w σ x) := by sorry
