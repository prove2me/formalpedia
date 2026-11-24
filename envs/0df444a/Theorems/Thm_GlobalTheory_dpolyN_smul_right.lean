-- Prove2me | Theorems.Thm_GlobalTheory_dpolyN_smul_right
-- name    : GlobalTheory.dpolyN_smul_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:42.28749+00:00
-- url     : https://prove2.me/theorems/beb7ba59-03d7-4e18-98cf-f8ad457a6ffe
-- title:
--   Global Theory: dpoly N smul right
-- statement:
--   The Global Theory construction uses the dpoly N smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NablaValueCopiesBilinear.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NablaValueCopiesBilinear.lean#L65-L68

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

theorem GlobalTheory.dpolyN_smul_right (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (t : R) (f : PS R n d) :
    DpolyN F cp u P (t • f) = t • DpolyN F cp u P f := by sorry
