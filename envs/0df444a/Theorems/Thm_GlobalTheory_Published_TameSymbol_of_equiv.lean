-- Prove2me | Theorems.Thm_GlobalTheory_Published_TameSymbol_of_equiv
-- name    : GlobalTheory.Published.TameSymbol.of_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:57.682046+00:00
-- url     : https://prove2.me/theorems/817be91d-df69-4d69-a795-c06a9fbbd33a
-- title:
--   Tame Symbol: of equiv
-- statement:
--   The Tame Symbol construction uses the of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean#L157-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/ContinuousCycMod.lean#L157-L182

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.Published
open GlobalTheory.TameQuot

theorem GlobalTheory.Published.TameSymbol.of_equiv (hT : TameSymbol) {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (hq : normV v ≡ 1 [MOD l ^ n]) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ n))
    (e : H2 (muDec F A l n) ≃ₗ[ZMod (l ^ n)] ZMod (l ^ n)) :
    ∃ u : (ZMod (l ^ n))ˣ, ∀ x : Ω, IsUnifRoot v (l ^ n) x →
      ∀ (γ : Dec (F := F) A) (c : ZMod (l ^ n)), (γ : G F Ω) ∈ Ine (F := F) A →
        (γ : G F Ω) x = ζ ^ c.val * x →
        ∀ φ : Dec (F := F) A, IsFrob A (normV v) (φ : G F Ω) →
        ∀ (z : Z1 (trivDec F A l n)) (y : Z1 (muDec F A l n)),
          (Submodule.Quotient.mk y : H1 (muDec F A l n)) ∈
            H1ur (muDec F A l n) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) →
          c * e (cupMu F A l n (Submodule.Quotient.mk z) (Submodule.Quotient.mk y)) =
            u * (z.1 γ * y.1 φ) := by sorry
