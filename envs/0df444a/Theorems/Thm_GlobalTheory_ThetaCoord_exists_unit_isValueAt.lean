-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCoord_exists_unit_isValueAt
-- name    : GlobalTheory.ThetaCoord.exists_unit_isValueAt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:16:39.887587+00:00
-- url     : https://prove2.me/theorems/a0fa519d-6fcc-48e7-9a50-b4e2a088d207
-- title:
--   Theta Coord: exists unit is Value At
-- statement:
--   The Theta Coord construction uses the exists unit is Value At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverOfSubsingleton.lean#L316-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverOfSubsingleton.lean#L316-L408

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaCoord
open CommPairing GlobalLift VVRank
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T T' : Over S} {k : ℤ}

theorem GlobalTheory.ThetaCoord.exists_unit_isValueAt (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {a b : ℤ} {m r n q q' : ℕ}
    (hn : n = r * m) (hq : q ∣ q') (ho : Odd q') {th th' : LB.Sec (LPow A L 1 T)} {ρ : Γ(T.left, ⊤)}
    (hρ : SecM.ofSec A th = ρ • SecM.ofSec A th')
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![b, -1])} (hα : α.IsGen)
    {α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ n).left] ![a, -1])} (hα' : α'.IsGen)
    {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (hs : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) b 1 α th s)
    (hs' : IsTwistPull A L (mulT A T n) (snd T A ^ n) (lift_snd _ _) a 1 α' th' s')
    {τ₀ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ A).left) (fun _ => a))} (hτ₀ : τ₀.IsGen)
    {Z h : T ⟶ A} (hh : Z ^ r = h) {UZ : ThetaGrp A L a T} (hZ : SymLift A L a q' Z UZ)
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => h.left) (fun _ => b))} (hτ : τ.IsGen) :
    ∃ u : Γ(T.left, ⊤)ˣ, ∀ (Y : T ⟶ A) (U : ThetaGrp A L b T) (t : LB.Sec (LPow A L b T)) (W : ThetaGrp A L a T)
      (t' : LB.Sec (LPow A L a T)) (w : Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)ˣ), Y ^ q' = 1 →
      SymLift A L b q (Y ^ r) U → IsActOf A L b U s t → SymLift A L a q' (Y * Z) W → IsActOf A L a W s' t' →
      IsValueAt A L a t' 1 τ₀ w → WeilIs A L a Z Y c →
      IsValueAt A L b t h τ (ρ * u * (c ^ ((q' + 1) / 2) : Γ(T.left, ⊤)ˣ) * w) := by sorry
