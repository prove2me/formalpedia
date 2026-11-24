-- Prove2me | Theorems.Thm_GlobalTheory_dpolyN_C_mul_left
-- name    : GlobalTheory.dpolyN_C_mul_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:16:45.438794+00:00
-- url     : https://prove2.me/theorems/4c028397-3228-41eb-a781-5ade42687556
-- title:
--   Global Theory: dpoly N C mul left
-- statement:
--   The Global Theory construction uses the dpoly N C mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NablaValueCopiesBilinear.lean#L81-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NablaValueCopiesBilinear.lean#L81-L91

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NablaValueCopiesBilinear
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
open GlobalTheory
variable {R : Type} [CommRing R] {d n : ℕ}
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.dpolyN_C_mul_left (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (t : R) (P : MvPolynomial ι R) (f : PS R n d) :
    DpolyN F cp u (MvPolynomial.C t * P) f = MvPowerSeries.C t * DpolyN F cp u P f := by sorry
