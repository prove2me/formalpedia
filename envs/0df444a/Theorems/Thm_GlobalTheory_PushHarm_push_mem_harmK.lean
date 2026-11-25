-- Prove2me | Theorems.Thm_GlobalTheory_PushHarm_push_mem_harmK
-- name    : GlobalTheory.PushHarm.push_mem_harmK
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:05.831579+00:00
-- url     : https://prove2.me/theorems/a68ca444-52cd-4ca8-9cc6-b3d04a5c6369
-- title:
--   Push Harm: push mem harm K
-- statement:
--   The Push Harm construction uses the push mem harm K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PushMemHarmK.lean#L102-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PushMemHarmK.lean#L102-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PushMemHarmK
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
open GlobalTheory GlobalTheory.PushHarm
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n : ℕ}

theorem GlobalTheory.PushHarm.push_mem_harmK : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (c : Coeff l) (n : ℕ) (γ : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.IsUnitary γ →
    P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ P ∈
      harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) := by sorry
