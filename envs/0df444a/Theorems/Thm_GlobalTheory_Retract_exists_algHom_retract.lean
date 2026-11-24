-- Prove2me | Theorems.Thm_GlobalTheory_Retract_exists_algHom_retract
-- name    : GlobalTheory.Retract.exists_algHom_retract
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:21:11.399583+00:00
-- url     : https://prove2.me/theorems/f5a25204-7e58-41d9-9052-8b433fec1930
-- title:
--   Retract: exists alg Hom retract
-- statement:
--   The Retract construction uses the exists alg Hom retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L142-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L142-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}

theorem GlobalTheory.Retract.exists_algHom_retract (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
    {U : X.Opens} {V : Y.Opens} {W : S.Opens}
    (hUV : U ≤ i ⁻¹ᵁ V) (hVU : V ≤ r ⁻¹ᵁ U) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    letI := (f.appLE W U hUW).hom.toAlgebra
    letI := (g.appLE W V hVW).hom.toAlgebra
    ∃ (s : Γ(X, U) →ₐ[Γ(S, W)] Γ(Y, V)) (p : Γ(Y, V) →ₐ[Γ(S, W)] Γ(X, U)),
      s.toRingHom = (r.appLE U V hVU).hom ∧ p.toRingHom = (i.appLE V U hUV).hom ∧
        p.comp s = AlgHom.id _ _ := by sorry
