-- Prove2me | Theorems.Thm_GrothendieckLB_mixed_avgCorr_coefficients
-- name    : GrothendieckLB.mixed_avgCorr_coefficients
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T04:00:32.862715+00:00
-- url     : https://prove2.me/theorems/4f137e88-9cb3-4dd8-9f89-b6b734820d1b
-- title:
--   Degree-one and degree-three coefficients average through a mixed scheme
-- statement:
--   Let $\mu$ be a $d$-dimensional mixed rounding scheme, with averaged correlation function $H_\mu$. Its first and third Taylor coefficients are obtained by averaging the coefficients of the sampled sign pairs:
--   $$
--   [t]H_\mu=\mathbb E_{(f,g)\sim\mu}[t]H_{f,g},\qquad
--   [t^3]H_\mu=\mathbb E_{(f,g)\sim\mu}[t^3]H_{f,g}.
--   $$
--   The two sampled coefficient functions are integrable with respect to the probability measure $\mu$, and
--   $$
--   [t]H_\mu\le1.
--   $$
--   Thus the finite-degree affine expressions used in Sections 8–10 can be averaged directly. The linear upper bound follows from the sign-pair estimate $|b_1(f,g)|\le1$ together with the first averaging identity.
--
--   **Formalization Note** The integrability clauses record the analytic inputs needed to use Bochner-integral monotonicity when averaging the affine inequality. No oddness assumption is made on the sampled sign pairs.
-- source:
--   Saha, Li, Xue, Chaudhuri, Klivans, Kothari, Meka, New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158, Section 7 coefficient formulas p.31; Section 9 introductory paragraph p.41 ('coefficients depend linearly on the correlation function'); Definition 10.1 p.42; linear-coefficient bound in the proof of the lower bound p.43.

import Mathlib
import Definitions.Def_GrothendieckLB_IsLimitingMixed
open MeasureTheory

namespace GrothendieckLB

/-- The degree-one and degree-three Taylor coefficients of an averaged correlation function are the corresponding probability integrals, these coefficient functions are integrable, and the averaged linear coefficient is at most one. -/

theorem mixed_avgCorr_coefficients {d : ℕ} (S : MixedScheme d) :
    taylorCoeff 1 S.avgCorr =
        ∫ ω, taylorCoeff 1 (pairCorr (S.F ω) (S.G ω)) ∂S.μ ∧
      taylorCoeff 3 S.avgCorr =
        ∫ ω, taylorCoeff 3 (pairCorr (S.F ω) (S.G ω)) ∂S.μ ∧
      Integrable (fun ω => taylorCoeff 1 (pairCorr (S.F ω) (S.G ω))) S.μ ∧
      Integrable (fun ω => taylorCoeff 3 (pairCorr (S.F ω) (S.G ω))) S.μ ∧
      taylorCoeff 1 S.avgCorr ≤ 1 := by sorry
