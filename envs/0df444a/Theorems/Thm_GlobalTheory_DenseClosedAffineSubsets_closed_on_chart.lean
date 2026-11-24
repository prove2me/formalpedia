-- Prove2me | Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_closed_on_chart
-- name    : GlobalTheory.DenseClosedAffineSubsets.closed_on_chart
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:43:45.841052+00:00
-- url     : https://prove2.me/theorems/bd239a16-331c-477b-a25b-bbdc98adaadd
-- title:
--   Dense Closed Affine Subsets: closed on chart
-- statement:
--   The Dense Closed Affine Subsets construction uses the closed on chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L270-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L270-L302

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.DenseClosedAffineSubsets.closed_on_chart {S W P X : Scheme.{0}} (f : W ⟶ S) (s : P ⟶ S) [IsSeparated f]
    (U O : W.Opens) (hUO : U ≤ O) (φ : U.toScheme ⟶ P) (ι : X ⟶ pullback f s)
    [IsClosedImmersion ι] (j : U.toScheme ⟶ X) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (h₁ : j ≫ ι ≫ pullback.fst f s = U.ι) (h₂ : j ≫ ι ≫ pullback.snd f s = φ)
    {σ : Type} (g : σ → Γ(O.toScheme, ⊤))
    [IsClosedImmersion (AffineSpace.homOfVector (O.ι ≫ f) g)]
    (D : P.Opens) (r : σ → Γ(D.toScheme, ⊤))
    (hr : ∀ (V : Scheme.{0}) (a : V ⟶ U) (b : V ⟶ D), a ≫ φ = b ≫ D.ι →
      ∀ i, b.appTop (r i) = a.appTop ((W.homOfLE hUO).appTop (g i))) :
    IsClosedImmersion ((ι ≫ pullback.snd f s) ∣_ D) := by sorry
