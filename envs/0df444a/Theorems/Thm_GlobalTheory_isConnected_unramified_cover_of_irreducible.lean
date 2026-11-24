-- Prove2me | Theorems.Thm_GlobalTheory_isConnected_unramified_cover_of_irreducible
-- name    : GlobalTheory.isConnected_unramified_cover_of_irreducible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:34.63828+00:00
-- url     : https://prove2.me/theorems/41afc02f-4a76-44b7-b726-1202cdb95bd0
-- title:
--   Global Theory: is Connected unramified cover of irreducible
-- statement:
--   The Global Theory construction uses the is Connected unramified cover of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedUnramifiedCoverOfIrreducible.lean#L122-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsConnectedUnramifiedCoverOfIrreducible.lean#L122-L207

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsConnectedUnramifiedCoverOfIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open SimpleRoots

theorem GlobalTheory.isConnected_unramified_cover_of_irreducible :
    (∀ (d : ℕ) (q : MvPolynomial (Fin d) ℂ), q ≠ 0 →
      IsConnected {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0} ∧
        Dense {x : Fin d → ℂ | MvPolynomial.eval x q ≠ 0}) →
    (∀ (d m : ℕ) (q : MvPolynomial (Fin d) ℂ) (f : (Fin d → ℂ) → ℂ) (C : ℝ), q ≠ 0 →
      DifferentiableOn ℂ f {x | MvPolynomial.eval x q ≠ 0} →
      (∀ x, MvPolynomial.eval x q ≠ 0 → ‖f x‖ ≤ C * (1 + ‖x‖) ^ m) →
      ∃ p : MvPolynomial (Fin d) ℂ, ∀ x, MvPolynomial.eval x q ≠ 0 → f x = MvPolynomial.eval x p) →
    (∀ (d : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ),
      p.Monic → Irreducible p → q ≠ 0 →
      (∀ x y, MvPolynomial.eval x q ≠ 0 → (p.map (MvPolynomial.eval x)).eval y = 0 →
        (p.map (MvPolynomial.eval x)).derivative.eval y ≠ 0) →
      IsConnected {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧
        (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}) := by sorry
