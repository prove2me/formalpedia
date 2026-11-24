-- Prove2me | Theorems.Thm_GlobalTheory_dpolyN_map
-- name    : GlobalTheory.dpolyN_map
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:17:59.608078+00:00
-- url     : https://prove2.me/theorems/51de1833-5013-477a-a07d-0253f3f8b85d
-- title:
--   Global Theory: dpoly N map
-- statement:
--   The Global Theory construction uses the dpoly N map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MapDofNIterate.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MapDofNIterate.lean#L61-L67

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MapDofNIterate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory

theorem GlobalTheory.dpolyN_map : ∀ (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (d n : ℕ) (F : Fin d → PS S 2 d) (κ : Type) [Fintype κ] (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S) (f : PS S n d), DpolyN (fun i => MvPowerSeries.map ψ (F i)) cp (fun l j => ψ (u l j)) (MvPolynomial.map ψ P) (MvPowerSeries.map ψ f) = MvPowerSeries.map ψ (DpolyN F cp u P f) := by sorry
