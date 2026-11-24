-- Prove2me | Theorems.Thm_GlobalTheory_ConvexCutOff_term_eq
-- name    : GlobalTheory.ConvexCutOff.term_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:49.523464+00:00
-- url     : https://prove2.me/theorems/6ffded8f-657c-44d8-a6e5-0d156e2ba1e6
-- title:
--   Convex Cut Off: term eq
-- statement:
--   The Convex Cut Off construction uses the term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolyDerivRenameOfConvex.lean#L141-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolyDerivRenameOfConvex.lean#L141-L149

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolyDerivRenameOfConvex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory GlobalTheory.ConvexCutOff

theorem GlobalTheory.ConvexCutOff.term_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {F : V → ℂ} {x : V}
    (hs : ∀ (n : ℕ) (v : Fin n → V) (σ : Equiv.Perm (Fin n)),
      iteratedFDeriv ℂ n F x (v ∘ σ) = iteratedFDeriv ℂ n F x v)
    {n m : ℕ} (v : Fin n → V) (w : Fin m → V) (h : (List.ofFn v).Perm (List.ofFn w)) :
    iteratedFDeriv ℂ n F x v = iteratedFDeriv ℂ m F x w := by sorry
