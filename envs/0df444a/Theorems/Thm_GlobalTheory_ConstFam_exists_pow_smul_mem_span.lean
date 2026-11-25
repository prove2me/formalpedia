-- Prove2me | Theorems.Thm_GlobalTheory_ConstFam_exists_pow_smul_mem_span
-- name    : GlobalTheory.ConstFam.exists_pow_smul_mem_span
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:58:16.720027+00:00
-- url     : https://prove2.me/theorems/89e64e06-952e-4d04-87f2-1269a2a349be
-- title:
--   Const Fam: exists pow smul mem span
-- statement:
--   The Const Fam construction uses the exists pow smul mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ConstFamComponentsBasisExpansion.lean#L141-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ConstFamComponentsBasisExpansion.lean#L141-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsBasisOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSmulMemSpanOfExpandsAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstFamComponentsBasisExpansion
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)
variable {A : PolAV (Spec (CommRingCat.of (FractionRing (PowerSeries k))))}
  {G : Over (Spec (CommRingCat.of (PowerSeries k)))} [GrpObj G] [IsCommMonObj G]
  (U : Unif (Ideal.span {PowerSeries.X}) P A G)
include hG hj

theorem GlobalTheory.ConstFam.exists_pow_smul_mem_span {C : Type} (rep : C → a.D₀.X) (hrep : ∀ α, ∃! x, ∃ mu, rep x + j • mu = α)
    {Idx : C → Type} (bas : ∀ x, Module.Basis (Idx x) k (SecBMod a.D₀ j (rep x))) (m : (Σ x, Idx x) → ℕ)
    (f : (Σ x, Idx x) → ∀ χ, SecBMod P.toPre j χ)
    (σ : (Σ x, Idx x) → SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ))))
    (hf : ∀ i : Σ x, Idx x, IsIntegralForm hW j (rep i.1) (bas i.1 i.2) (m i) (f i))
    (hE : ∀ i n, U.toUnifPre.ExpandsAt n j (σ i) (f i))
    (s : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (j : ℤ)))) :
    ∃ n : ℕ, (PowerSeries.X : PowerSeries k) ^ n • s ∈ Submodule.span (PowerSeries k) (Set.range σ) := by sorry
