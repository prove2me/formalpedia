-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_IsPullConst_eq_one
-- name    : GlobalTheory.ThetaFn.IsPullConst.eq_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:11.579988+00:00
-- url     : https://prove2.me/theorems/afbaec01-e0ef-4143-a6e0-28e6cf08bccd
-- title:
--   Is Pull Const: eq one
-- statement:
--   The Is Pull Const construction uses the eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L194-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L194-L209

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p}

theorem GlobalTheory.ThetaFn.IsPullConst.eq_one (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hrig : u.IsRig rig)
    {m : T ⊗ A ⟶ A} {Φ : (Fin g → ℂ) → Fin g → ℂ} (h0 : Φ 0 = 0)
    (hΦ : exAt u p 0 ≫ m.left = (u.ex 0).left) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} {c : ℂ}
    (hc : IsPullConst u p Φ a b α c)
    (hn : ∀ j : Fin 2 → L.ι, ⊤ ≤ exAt u p 0 ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
      valAt' (exAt u p 0) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
          valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 1) (rig.s fun _ => j 1).val ^ b =
        valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U fun _ => j 0) (rig.s fun _ => j 0).val ^ a) :
    c = 1 := by sorry
