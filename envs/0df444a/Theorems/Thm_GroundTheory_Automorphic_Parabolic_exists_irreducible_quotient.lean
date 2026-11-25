-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_irreducible_quotient
-- name    : GroundTheory.Automorphic.Parabolic.exists_irreducible_quotient
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:06.955604+00:00
-- url     : https://prove2.me/theorems/5bcff70e-66e5-4496-b2ea-c5f18f035dcb
-- title:
--   Parabolic: exists irreducible quotient
-- statement:
--   The Parabolic construction uses the exists irreducible quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L56-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L56-L120

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
variable {G : Type*} [Group G] {U : Type*} [AddCommGroup U] [Module ℂ U]
  {τ : Representation ℂ G U}

theorem GroundTheory.Automorphic.Parabolic.exists_irreducible_quotient [Nontrivial U] (S : Finset U)
    (hS : Submodule.span ℂ {x | ∃ g, ∃ s ∈ S, x = τ g s} = ⊤) :
    ∃ (Y : Submodule ℂ U) (hY : ∀ g, Y ≤ Y.comap (τ g)),
      (Representation.quotient τ Y hY).IsIrreducible := by sorry
