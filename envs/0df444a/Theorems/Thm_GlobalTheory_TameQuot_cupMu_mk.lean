-- Prove2me | Theorems.Thm_GlobalTheory_TameQuot_cupMu_mk
-- name    : GlobalTheory.TameQuot.cupMu_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:31.694025+00:00
-- url     : https://prove2.me/theorems/f096ff9a-65fa-4c36-a17c-db4c2469c507
-- title:
--   Tame Quot: cup Mu mk
-- statement:
--   The Tame Quot construction uses the cup Mu mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean#L78-L89

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.TameQuot
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem GlobalTheory.TameQuot.cupMu_mk {A : ValuationSubring Ω} {l : ℕ} [Fact l.Prime] {n : ℕ}
    (z : Z1 (trivDec F A l n)) (y : Z1 (muDec F A l n)) (f : Z2 (muDec F A l n))
    (hf : ∀ g h, f.1 (g, h) = z.1 g * muDec F A l n g (y.1 h)) :
    cupMu F A l n (Submodule.Quotient.mk z) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk f := by sorry
