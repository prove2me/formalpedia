-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCoverGrowth_exists_local_roots
-- name    : GlobalTheory.FiniteCoverGrowth.exists_local_roots
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:29:29.519802+00:00
-- url     : https://prove2.me/theorems/33f550f1-8fa2-4e61-b986-0445cc60a403
-- title:
--   Finite Cover Growth: exists local roots
-- statement:
--   The Finite Cover Growth construction uses the exists local roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IntegralAndRationalOfPolynomialGrowth.lean#L144-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IntegralAndRationalOfPolynomialGrowth.lean#L144-L173

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.FiniteCoverGrowth

theorem GlobalTheory.FiniteCoverGrowth.exists_local_roots {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (hp : p.Monic)
    (x₀ : Fin d → ℂ) (hs : (p.map (MvPolynomial.eval x₀)).Separable) :
    ∃ y : Fin p.natDegree → (Fin d → ℂ) → ℂ, (∀ i, DifferentiableAt ℂ (y i) x₀) ∧
      ∀ᶠ x in 𝓝 x₀, Function.Injective (fun i => y i x) ∧
        (p.map (MvPolynomial.eval x)).roots.toFinset = Finset.univ.image (fun i => y i x) := by sorry
