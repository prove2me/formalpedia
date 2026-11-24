-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayEx_exists_group
-- name    : GlobalTheory.Mem.RayEx.exists_group
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:45:23.978788+00:00
-- url     : https://prove2.me/theorems/f07c7ae4-d2e6-4654-ad70-8d8177c69387
-- title:
--   Ray Ex: exists group
-- statement:
--   The Ray Ex construction uses the exists group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L141-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L141-L146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayEx
open NumberField IsDedekindDomain
variable {R : Type} [CommRing R] [IsDedekindDomain R] (m : Ideal R)
variable {m}

theorem GlobalTheory.Mem.RayEx.exists_group (hm : m ≠ ⊤) [Finite (R ⧸ m)] [Finite (ClassGroup R)] :
    ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G) (φ : S m →* G), Function.Surjective φ ∧
      ∀ I J, φ I = φ J ↔ Rel m I.1 J.1 := by sorry
