-- Prove2me | Theorems.Thm_GlobalTheory_BorelAlg_exists_isHomogeneous_of_equivariant
-- name    : GlobalTheory.BorelAlg.exists_isHomogeneous_of_equivariant
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:33.994158+00:00
-- url     : https://prove2.me/theorems/d9233c35-931b-459c-96d6-8f6bd1b7827b
-- title:
--   Borel Alg: exists is Homogeneous of equivariant
-- statement:
--   The Borel Alg construction uses the exists is Homogeneous of equivariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L288-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean#L288-L293

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.BorelAlg
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem GlobalTheory.BorelAlg.exists_isHomogeneous_of_equivariant :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (K : Type) [Field K] (a : (E →+* ℂ) × ℕ → ℕ) (f : ArcS Dw K), (∀ (T : Type) [Field T] (φ ψ : ArcS Dw K →+* T) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T), (∀ g : LaurentSeries K, φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) _ (MvPolynomial.C g)) = ψ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) _ (MvPolynomial.C g))) → (∀ τ i j, i < j → b τ i j = 0) → (∀ τ i k, ψ (arcX Dw K τ i k) = ∑ j, b τ i j * φ (arcX Dw K τ j k)) → ψ f = (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) * φ f) → ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K), algebraMap _ (ArcS Dw K) P = f ∧ P.IsHomogeneous (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by sorry
