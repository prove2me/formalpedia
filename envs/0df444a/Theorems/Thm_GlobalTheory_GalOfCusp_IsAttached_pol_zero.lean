-- Prove2me | Theorems.Thm_GlobalTheory_GalOfCusp_IsAttached_pol_zero
-- name    : GlobalTheory.GalOfCusp.IsAttached.pol_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:05:59.116287+00:00
-- url     : https://prove2.me/theorems/b165d3a5-f18c-5260-be6c-03ec19632d82
-- title:
--   Is Attached: pol zero
-- statement:
--   The Is Attached construction uses the pol zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/TrivialOnInertiaOfUnr.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/TrivialOnInertiaOfUnr.lean#L90-L92

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
variable {A}
variable {i : N.Loc} {a : ℕ} {π : A.CG a} {s : ℝ} {r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))}

theorem GlobalTheory.GalOfCusp.IsAttached.pol_zero (h : IsAttached A i π 0 r) {c : N.Om ≃+* N.Om} (hc : IsCMConjOm H.E N.Om c) :
    IsConjDual c r (cycBar H.E N.Om (N.l i) ^ (1 - (a : ℤ))) := by sorry
