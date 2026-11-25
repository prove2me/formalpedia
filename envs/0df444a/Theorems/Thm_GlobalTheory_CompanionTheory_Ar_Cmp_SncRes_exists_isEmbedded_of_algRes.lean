-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_exists_isEmbedded_of_algRes
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.exists_isEmbedded_of_algRes
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:00:58.833368+00:00
-- url     : https://prove2.me/theorems/c71872db-c1b8-48cb-9802-ab338ffa06fa
-- title:
--   Snc Res: exists is Embedded of alg Res
-- statement:
--   The Snc Res construction uses the exists is Embedded of alg Res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncModelEmbeddedLogResolution.lean#L36-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncModelEmbeddedLogResolution.lean#L36-L152

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterAlgRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Immersion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbeddedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionTransitionPolynomialStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndConeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionLocalChartPolynomialStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionBoundaryNormalCrossingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncModelEmbeddedLogResolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.exists_isEmbedded_of_algRes {P J : Ideal (MRing ι)} {e : ℕ} (hJ : IsMultiHomogIdeal J)
    (hJP : ¬ J ≤ P) (hPC : ∀ f : MRing ι, map (Int.castRingHom ℂ) f ∈ pC P → f ∈ P)
    (R : ReciprocityTheory.AnForm.R.AlgRes ι (pC P) (pC J) e)
    (hsurj : ∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC P), ∃ i, ∃ x ∈ R.src i,
      ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (R.coord i x) (R.lift i q)) z)
    (hinj : ∀ i j, ∀ x ∈ R.src i, ∀ x' ∈ R.src j,
      ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (R.coord i x) (R.lift i q))
        (fun q => eval (R.coord j x') (R.lift j q)) → x = x')
    (hinv : ∀ i, ∀ x ∈ R.src i, ∀ p : (k : K) → ι k, (∀ k, eval (R.coord i x) (R.lift i ⟨k, p k⟩) ≠ 0) →
      ∃ O : Set R.M, IsOpen O ∧ x ∈ O ∧ O ⊆ R.src i ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ)
        (F : Fin (R.amb i) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O,
          (∀ k, eval (R.coord i y) (R.lift i ⟨k, p k⟩) ≠ 0) ∧
          eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) q ≠ 0 ∧
          ∀ l, R.coord i y l * eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) q =
            eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) (F l)) :
    ∃ R' : AnLogRes P J e, IsEmbedded R'.A P R'.U R'.lift := by sorry
