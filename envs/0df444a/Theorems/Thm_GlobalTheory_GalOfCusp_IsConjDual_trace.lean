-- Prove2me | Theorems.Thm_GlobalTheory_GalOfCusp_IsConjDual_trace
-- name    : GlobalTheory.GalOfCusp.IsConjDual.trace
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:48:37.424986+00:00
-- url     : https://prove2.me/theorems/fd091d1f-61f4-4fe2-8fa9-b91db66749d6
-- title:
--   Is Conj Dual: trace
-- statement:
--   The Is Conj Dual construction uses the trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/TrivialOnInertiaOfUnr.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/TrivialOnInertiaOfUnr.lean#L21-L26

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
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {k : Type} [Field k] {a : ℕ}

theorem GlobalTheory.GalOfCusp.IsConjDual.trace {c : Ω ≃+* Ω} {r : G E Ω →* GL (Fin a) k} {μ : G E Ω →* kˣ} (h : IsConjDual c r μ)
    {g g' : G E Ω} (hg : ∀ x, g' x = c (g (c.symm x))) :
    (r g' : Matrix (Fin a) (Fin a) k).trace = μ g * (r g⁻¹ : Matrix (Fin a) (Fin a) k).trace := by sorry
