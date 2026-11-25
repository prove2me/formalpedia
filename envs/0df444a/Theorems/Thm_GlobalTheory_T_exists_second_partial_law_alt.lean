-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_second_partial_law_alt
-- name    : GlobalTheory.T.exists_second_partial_law_alt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:40:17.919216+00:00
-- url     : https://prove2.me/theorems/090d3e29-42f5-49d6-9ca6-10d9159279e6
-- title:
--   T: exists second partial law alt
-- statement:
--   The T construction uses the exists second partial law alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsSecondPartialLawStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsSecondPartialLawStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLawStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_second_partial_law_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → FrTrunc t x0 d x e → FrAxes t x0 d x e → ∃ ph2 : PS S 3 d, ∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))) := by sorry
