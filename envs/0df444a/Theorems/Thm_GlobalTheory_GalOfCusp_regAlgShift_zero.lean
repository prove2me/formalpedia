-- Prove2me | Theorems.Thm_GlobalTheory_GalOfCusp_regAlgShift_zero
-- name    : GlobalTheory.GalOfCusp.regAlgShift_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:50:40.598592+00:00
-- url     : https://prove2.me/theorems/cf81f8d8-4cb7-414c-b186-82aa3cc8bcf2
-- title:
--   Gal Of Cusp: reg Alg Shift zero
-- statement:
--   The Gal Of Cusp construction uses the reg Alg Shift zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/TrivialOnInertiaOfUnr.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/TrivialOnInertiaOfUnr.lean#L45-L47

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__TrivialOnInertiaOfUnr_d5f82434e8467b70
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GalOfCusp
open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open scoped Matrix
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)

theorem GlobalTheory.GalOfCusp.regAlgShift_zero {a : ℕ} (π : A.CG a) : RegAlgShift A π 0 ↔ A.ralg π := by sorry
