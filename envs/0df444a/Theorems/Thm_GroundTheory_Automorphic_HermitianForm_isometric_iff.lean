-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isometric_iff
-- name    : GroundTheory.Automorphic.HermitianForm.isometric_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:22.334292+00:00
-- url     : https://prove2.me/theorems/1f45ea00-8a64-5846-aedb-ebd5dbc6fdec
-- title:
--   Hermitian Form: isometric iff
-- statement:
--   The Hermitian Form construction uses the isometric iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianClassification.lean#L236-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianClassification.lean#L236-L299

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianDisc
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWittExtension
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSplit
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianClassification
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
open Module GroundTheory.LocalField ValuativeRel IsLocalRing Polynomial
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F}
variable {E : Type*} [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [Algebra.IsSeparable F E]
open GroundTheory.Automorphic.HermitianForm
variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']

theorem GroundTheory.Automorphic.HermitianForm.isometric_iff [FiniteDimensional E V] [FiniteDimensional E V'] (h : HermitianForm F E V)
    (h' : HermitianForm F E V') :
    Isometric h h' ↔ finrank E V = finrank E V' ∧ h.disc = h'.disc := by sorry
