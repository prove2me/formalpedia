-- Prove2me | Theorems.Thm_GlobalTheory_LevelMoveTest_carried_generator_unique
-- name    : GlobalTheory.LevelMoveTest.carried_generator_unique
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:03:07.984679+00:00
-- url     : https://prove2.me/theorems/b408c56a-1191-4b9d-ae20-11bd711ba742
-- title:
--   Level Move Test: carried generator unique
-- statement:
--   The Level Move Test construction uses the carried generator unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/CarriedGeneratorUnique.lean#L34-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/CarriedGeneratorUnique.lean#L34-L66

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_LevelGroupEqTopOfCoprime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelActionOverlapLeSourceChart
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_CarriedGeneratorUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevelMoveTest
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem GlobalTheory.LevelMoveTest.carried_generator_unique {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (x : Sp S ⟶ Xo.X) (pm : Gx x ⟶ Gx (x ≫ ρ))
    (hf : pm ≫ (fst (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (hs : pm ≫ (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ ν.φ)
    (s' s'' : LB.Sec (PPx (x ≫ ρ)))
    (h : ∀ (i j : Xo.univ.t.PP.L.ι) (W : (Gx x).Opens),
        W = (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ
          ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)) →
        ∀ (h₁ : W ≤ pm ⁻¹ᵁ (PPx (x ≫ ρ)).U (fun _ => i)),
        (pm.appLE ((PPx (x ≫ ρ)).U (fun _ => i)) W h₁).hom (s'.f (fun _ => i)) =
        (pm.appLE ((PPx (x ≫ ρ)).U (fun _ => i)) W h₁).hom (s''.f (fun _ => i)))
    (i : Xo.univ.t.PP.L.ι) : s'.f (fun _ => i) = s''.f (fun _ => i) := by sorry
