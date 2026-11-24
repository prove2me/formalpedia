-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFn_IsPullConst_fn_eq
-- name    : GlobalTheory.ThetaFn.IsPullConst.fn_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:00.396197+00:00
-- url     : https://prove2.me/theorems/9fedfcef-9e2a-4b06-8cb8-44cd7b136a0d
-- title:
--   Is Pull Const: fn eq
-- statement:
--   The Is Pull Const construction uses the fn eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L162-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean#L162-L177

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

theorem GlobalTheory.ThetaFn.IsPullConst.fn_eq (hL : L.IsLB) {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A}
    {hm : ψ ≫ snd T A = m} {Φ : (Fin g → ℂ) → Fin g → ℂ}
    (hψ : ∀ z, exAt u p z ≫ ψ.left = exAt u p (Φ z)) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} {c : ℂ}
    (hc : IsPullConst u p Φ a b α c) {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (ht : IsTwistPull A L ψ m hm a b α s s') {θ θ' : (Fin g → ℂ) → ℂ}
    (h : IsFnAt u p b s θ) (h' : IsFnAt u p a s' θ') (z : Fin g → ℂ) : θ' z = c * θ (Φ z) := by sorry
