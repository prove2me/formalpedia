-- Prove2me | Theorems.Thm_GlobalTheory_points_eq_image_hypersurface
-- name    : GlobalTheory.points_eq_image_hypersurface
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:13:45.441811+00:00
-- url     : https://prove2.me/theorems/7f149946-a85e-4794-8c92-35bac01cb439
-- title:
--   Global Theory: points eq image hypersurface
-- statement:
--   The Global Theory construction uses the points eq image hypersurface property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsConnectedPrincipalOpen.lean#L35-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsConnectedPrincipalOpen.lean#L35-L116

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsConnectedPrincipalOpen
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
open GlobalTheory

theorem GlobalTheory.points_eq_image_hypersurface {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
    (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (q q' : MvPolynomial (Fin d) ℂ)
    (hp : ∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r)
    (r : A → Polynomial (MvPolynomial (Fin d) ℂ))
    (hr : ∀ b, j q * b = (r b).eval₂ j.toRingHom a) :
    {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x (j (q * q')) ≠ 0} =
      (fun (z : (Fin d → ℂ) × ℂ) (b : A) => evalPair z (r b) / MvPolynomial.eval z.1 q) ''
        {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 (q * q') ≠ 0 ∧
          (p.map (MvPolynomial.eval z.1)).eval z.2 = 0} := by sorry
