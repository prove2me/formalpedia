-- Prove2me | Theorems.Thm_GlobalTheory_ThetaLeast_exists_combination_integers
-- name    : GlobalTheory.ThetaLeast.exists_combination_integers
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:49:22.142715+00:00
-- url     : https://prove2.me/theorems/7465e3da-7256-4c67-82a3-bd5f987e08b8
-- title:
--   Theta Least: exists combination integers
-- statement:
--   The Theta Least construction uses the exists combination integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCombinationIntegers.lean#L78-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCombinationIntegers.lean#L78-L132

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCombinationOfMemHaO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_VVAlgebraMapNonnegDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCombinationIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.ThetaLeast

theorem GlobalTheory.ThetaLeast.exists_combination_integers (K : Type) [Field K] [NumberField K] (T : CDVR) (io : K →+* T.Fr)
    (Ty : Type) (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (P : MvPolynomial (Letter Ty r n) T.Fr) (hP : P ∈ HaO r n T.Fr (algebraMap T.V T.Fr).range cc isX a) :
    ∃ (s : ℕ) (c : Fin s → T.V) (Q : Fin s → MvPolynomial (Letter Ty r n) K),
      (∀ j, Q j ∈ HaO r n K (integralClosure ℤ K).toSubring cc isX a) ∧
      P = ∑ j, algebraMap T.V T.Fr (c j) • MvPolynomial.map io (Q j) := by sorry
