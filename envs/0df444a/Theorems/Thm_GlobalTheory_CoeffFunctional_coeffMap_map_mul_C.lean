-- Prove2me | Theorems.Thm_GlobalTheory_CoeffFunctional_coeffMap_map_mul_C
-- name    : GlobalTheory.CoeffFunctional.coeffMap_map_mul_C
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:15:22.930638+00:00
-- url     : https://prove2.me/theorems/9c66e48c-e333-477b-85bc-0181b0aa580b
-- title:
--   Coeff Functional: coeff Map map mul C
-- statement:
--   The Coeff Functional construction uses the coeff Map map mul C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemHHaOfCoeffFunctional.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemHHaOfCoeffFunctional.lean#L36-L41

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

theorem GlobalTheory.CoeffFunctional.coeffMap_map_mul_C (φ : L →ₗ[K] K) (A : MvPolynomial σ K) (c : L) :
    coeffMap φ (MvPolynomial.C c * MvPolynomial.map (algebraMap K L) A) =
      MvPolynomial.C (φ c) * A := by sorry
