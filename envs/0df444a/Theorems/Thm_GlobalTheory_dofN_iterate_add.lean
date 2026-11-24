-- Prove2me | Theorems.Thm_GlobalTheory_dofN_iterate_add
-- name    : GlobalTheory.dofN_iterate_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:06.429172+00:00
-- url     : https://prove2.me/theorems/9ebf0179-b368-4864-a605-7d2b9dc3e569
-- title:
--   Global Theory: dof N iterate add
-- statement:
--   The Global Theory construction uses the dof N iterate add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NablaValueCopiesBilinear.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/NablaValueCopiesBilinear.lean#L21-L26

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

theorem GlobalTheory.dofN_iterate_add (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (f g : PS R n d) :
    (DofN F b u)^[k] (f + g) = (DofN F b u)^[k] f + (DofN F b u)^[k] g := by sorry
