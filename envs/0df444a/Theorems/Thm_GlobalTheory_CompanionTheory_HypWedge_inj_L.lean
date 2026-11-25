-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HypWedge_inj_L
-- name    : GlobalTheory.CompanionTheory.HypWedge.inj_L
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:26:10.255526+00:00
-- url     : https://prove2.me/theorems/f89b58fd-0dad-4274-b338-6f9c9ee1cdbc
-- title:
--   Hyp Wedge: inj L
-- statement:
--   The Hyp Wedge construction uses the inj L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L262-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FormComponentOfWedgeClassZero.lean#L262-L291

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.CompanionTheory.HypWedge.inj_L (hs : Function.Surjective (toO F)) (hcl : Closed1 F = ⊤) (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F)
    (hτ : ∀ v, H1.mk F (cechDeRhamTotalCocyclesOne.fn F (τ v)) = v) (mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hmu : ∀ (f : Z1 F) (w : Glob1 F) (T T' : C) (φ : T ⟶ T'), mu (f ⊗ₜ w) T T' φ = f.1 T T' φ • w.1 T')
    (hmu3 : ∀ (t : Z1 F ⊗[R] Glob1 F) (β : A0 F),
      (∀ (T T' : C) (φ : T ⟶ T'), mu t T T' φ = β T' - p1 F φ (β T)) →
        (H1.mk F).rTensor (Glob1 F) t = 0)
    (nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (hnu : ∀ (a b : Glob1 F) (T : C), nu (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (u : H1 F ⊗[R] Glob1 F) (x : ⋀[R]^2 (Glob1 F)) (c : Tot1 F)
    (hc : dTot1 F c = (Lc hcl τ u + Nc hcl x).1) : u = 0 := by sorry
