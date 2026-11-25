-- Prove2me | Theorems.Thm_GlobalTheory_T_lattice_stable_almost_everywhere
-- name    : GlobalTheory.T.lattice_stable_almost_everywhere
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:35:58.608639+00:00
-- url     : https://prove2.me/theorems/6d0f31d5-6078-542a-8eec-ea391b66a731
-- title:
--   T: lattice stable almost everywhere
-- statement:
--   The T construction uses the lattice stable almost everywhere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeStableAlmostEverywhereStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeStableAlmostEverywhereStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhereStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lattice_stable_almost_everywhere : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ g : Matrix (Fin n) (Fin n) E, g.det ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v ↔ X ∈ latV b v) ∧ (∀ g : GL (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v ↔ X ∈ latV b v) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), consTup X ∈ latV b v ↔ X ∈ latV b v := by sorry
