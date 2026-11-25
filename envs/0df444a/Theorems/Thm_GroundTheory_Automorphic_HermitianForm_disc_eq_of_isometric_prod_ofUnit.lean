-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_disc_eq_of_isometric_prod_ofUnit
-- name    : GroundTheory.Automorphic.HermitianForm.disc_eq_of_isometric_prod_ofUnit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:30:06.982518+00:00
-- url     : https://prove2.me/theorems/66bdc603-66d8-404e-b33d-4409507163a7
-- title:
--   Hermitian Form: disc eq of isometric prod of Unit
-- statement:
--   The Hermitian Form construction uses the disc eq of isometric prod of Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianClassification.lean#L230-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianClassification.lean#L230-L234

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

theorem GroundTheory.Automorphic.HermitianForm.disc_eq_of_isometric_prod_ofUnit [FiniteDimensional E V] (h : HermitianForm F E V)
    {W : Submodule E V} {h₀ : HermitianForm F E W} {a : Fˣ}
    (H : Isometric ((ofUnit (E := E) a).prod h₀) h) :
    h.disc = QuotientGroup.mk a * h₀.disc := by sorry
