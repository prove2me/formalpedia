-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ModelFamilies_pmOf_apply
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.pmOf_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:09:22.152596+00:00
-- url     : https://prove2.me/theorems/b9cb948a-a8cc-44f9-a816-5bc96627d6d3
-- title:
--   Model Families: pm Of apply
-- statement:
--   The Model Families construction uses the pm Of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ModelFamilies.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ModelFamilies.lean#L66-L67

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ModelFamilies
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
variable {F : FamAt Xo c σ e} {r : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.pmOf_apply (M : ModelsOf F r) (k : Fin F.n) (x : Frame (M.X k).Ψ r) (a : (F.Di k).La) (j : Fin g) :
    pmOf M k x a j = perFr (M.X k) x (M.φ k a : Fin r → E) (relab c σ (e j).1) (e j).2 := by sorry
