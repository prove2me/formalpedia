-- Prove2me | Theorems.Thm_GlobalTheory_EvenPull_even_of_square
-- name    : GlobalTheory.EvenPull.even_of_square
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:07:28.429841+00:00
-- url     : https://prove2.me/theorems/f6f93ecf-5fe0-4997-9fd7-6f0daa5d97f9
-- title:
--   Even Pull: even of square
-- statement:
--   The Even Pull construction uses the even of square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PulledComparisonEven.lean#L106-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PulledComparisonEven.lean#L106-L195

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PulledComparisonEven
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.EvenPull

theorem GlobalTheory.EvenPull.even_of_square {T G B T' G' B' : Scheme.{0}} {L : LB G} {M : LB B} {L' : LB G'} {M' : LB B'}
    (hL : L.IsLB) (hM : M.IsLB)
    {f : T ⟶ G} {p : T ⟶ B} {iT : T ⟶ T} {iG : G ⟶ G} {iB : B ⟶ B}
    {f' : T' ⟶ G'} {p' : T' ⟶ B'} {iT' : T' ⟶ T'} {iG' : G' ⟶ G'} {iB' : B' ⟶ B'}
    {Ψ : G' ⟶ G} {Φ : B' ⟶ B} {h : T' ⟶ T}
    (hf : h ≫ f = f' ≫ Ψ) (hp : p' ≫ Φ = h ≫ p) (ih : iT' ≫ h = h ≫ iT)
    (iF : iT ≫ f = f ≫ iG) (iP : iT ≫ p = p ≫ iB) (iF' : iT' ≫ f' = f' ≫ iG') (iP' : iT' ≫ p' = p' ≫ iB')
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p'))
    (wL : LB.Iso L' (L.pull Ψ)) (wM : LB.Iso M' (M.pull Φ))
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]))
    (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]))
    (s' : LB.Gen (LB.LinComb L' (K := Fin 2) ![iG', 𝟙 G'] ![1, -1]))
    (σ' : LB.Gen (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]))
    (hs : PMaps wL (K := Fin 2) ![iG', 𝟙 G'] ![iG, 𝟙 G] ![1, -1] s' s Ψ)
    (hσ : PMaps wM (K := Fin 2) ![iB', 𝟙 B'] ![iB, 𝟙 B] ![1, -1] σ' σ Φ)
    (sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ T') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
      Φ (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → Ψ (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
      gw wM (r ≫ p') z jM jM' * gw w' r z jM' (fun _ => jL') =
        gw w (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ f') z jL jL')
    (ev : ∀ (jS : Fin 2 → L.ι) (jT : Fin 2 → M.ι),
      LB.Coh L (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS →
      LB.Coh M (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT →
      ∀ (V : T.Opens) (h₁ : V ≤ p ⁻¹ᵁ (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1]).U jT)
        (h₂ : V ≤ (M.pull p).U (fun _ => jT 1) ⊓ (L.pull f).U (fun _ => jS 1))
        (h₃ : V ≤ iT ⁻¹ᵁ ((M.pull p).U (fun _ => jT 0) ⊓ (L.pull f).U (fun _ => jS 0)))
        (h₄ : V ≤ f ⁻¹ᵁ (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1]).U jS),
        res h₁ (pullU p _ (σ.s jT)) * res h₂ (w.s (fun _ => jT 1, fun _ => jS 1)) =
          res h₃ (pullU iT _ (w.s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU f _ (s.s jS)))
    (jS' : Fin 2 → L'.ι) (jT' : Fin 2 → M'.ι)
    (V : T'.Opens) (h₁ : V ≤ p' ⁻¹ᵁ (LB.LinComb M' (K := Fin 2) ![iB', 𝟙 B'] ![1, -1]).U jT')
    (h₂ : V ≤ (M'.pull p').U (fun _ => jT' 1) ⊓ (L'.pull f').U (fun _ => jS' 1))
    (h₃ : V ≤ iT' ⁻¹ᵁ ((M'.pull p').U (fun _ => jT' 0) ⊓ (L'.pull f').U (fun _ => jS' 0)))
    (h₄ : V ≤ f' ⁻¹ᵁ (LB.LinComb L' (K := Fin 2) ![iG', 𝟙 G'] ![1, -1]).U jS') :
    res h₁ (pullU p' _ (σ'.s jT')) * res h₂ (w'.s (fun _ => jT' 1, fun _ => jS' 1)) =
      res h₃ (pullU iT' _ (w'.s (fun _ => jT' 0, fun _ => jS' 0))) * res h₄ (pullU f' _ (s'.s jS')) := by sorry
