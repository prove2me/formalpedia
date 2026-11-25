-- Prove2me | Theorems.Thm_GlobalTheory_LevelFibre_inGam_of_diff
-- name    : GlobalTheory.LevelFibre.inGam_of_diff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:03:21.44465+00:00
-- url     : https://prove2.me/theorems/7ff15bb5-65a4-4383-b0c7-ee4810c56202
-- title:
--   Level Fibre: in Gam of diff
-- statement:
--   The Level Fibre construction uses the in Gam of diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFibreSimplyTransitive.lean#L73-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFibreSimplyTransitive.lean#L73-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFibreSimplyTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LevelFibre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem GlobalTheory.LevelFibre.inGam_of_diff (l l₂ : Level H) (hd : l.Dvd l₂) (J J' : TateIso D k Q act e) (g : Sim D)
    (hg : ∀ n, 0 < n → (∀ a, J'.ev n a = J.ev n (g.f n a)) ∧ J'.ζ n = J.ζ n ^ g.ν n)
    (hζ : J'.ζ l₂.A = J.ζ l₂.A) (P P' : D.La → Q)
    (hP : ∀ a b, P (a + b) = P a * P b) (hP' : ∀ a b, P' (a + b) = P' a * P' b)
    (hk : ∀ a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D.La), P a = 1)
    (hk' : ∀ a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D.La), P' a = 1)
    (hJ : ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), P a = J.ev l₂.M a)
    (hJ' : ∀ a ∈ l₂.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), P' a = J'.ev l₂.M a)
    (hM : ∀ a, P a ^ (l₂.M / l.M) = P' a ^ (l₂.M / l.M))
    (hA : ∀ a, J.ev l₂.A a ^ (l₂.A / l.A) = J'.ev l₂.A a ^ (l₂.A / l.A)) :
    g.InGam l l₂ ∧ ∀ a, P' a = P (g.f l₂.M a) := by sorry
