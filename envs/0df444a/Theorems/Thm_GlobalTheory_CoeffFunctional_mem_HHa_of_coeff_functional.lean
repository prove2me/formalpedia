-- Prove2me | Theorems.Thm_GlobalTheory_CoeffFunctional_mem_HHa_of_coeff_functional
-- name    : GlobalTheory.CoeffFunctional.mem_HHa_of_coeff_functional
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:15:12.83838+00:00
-- url     : https://prove2.me/theorems/b9d72de6-b554-4323-bec5-6e45c3565c8b
-- title:
--   Coeff Functional: mem HHa of coeff functional
-- statement:
--   The Coeff Functional construction uses the mem HHa of coeff functional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemHHaOfCoeffFunctional.lean#L81-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemHHaOfCoeffFunctional.lean#L81-L101

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemHHaOfCoeffFunctional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoeffFunctional
open MvPolynomial
variable {σ K L : Type} [Field K] [Field L] [Algebra K L]
variable {T : Type} (r : T → ℕ) (n : ℕ)

theorem GlobalTheory.CoeffFunctional.mem_HHa_of_coeff_functional :
    ∀ (T : Type) (r : T → ℕ) (n : ℕ) (K C : Type) [Field K] [Field C] [Algebra K C] (φ : C →ₗ[K] K) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) C) (Q : MvPolynomial (Letter T r n) K), (∀ μ, Q.coeff μ = φ (P.coeff μ)) → P ∈ HHa r n C cc isX a → Q ∈ HHa r n K cc isX a := by sorry
