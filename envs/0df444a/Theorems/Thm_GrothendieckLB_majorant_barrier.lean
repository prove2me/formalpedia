-- Prove2me | Theorems.Thm_GrothendieckLB_majorant_barrier
-- name    : GrothendieckLB.majorant_barrier
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:37.162862+00:00
-- url     : https://prove2.me/theorems/75b4bf47-8edd-4516-8bf8-1b33ffb2c362
-- title:
--   General affine majorant barrier $\gamma\le\Gamma_\lambda$
-- statement:
--   Let $\lambda\ge\tfrac12$, and let $H$ be odd and analytic at the origin. Write $b_1=[t]H$ and $b_3=[t^3]H$, and suppose that
--
--   $$0<b_1\le1,\qquad b_3\ge(1+\lambda)b_1-\Bigl(\lambda+\frac56\Bigr).$$
--
--   Then every value $\gamma$ admissible for $H$ in the inverse-majorant sense satisfies
--
--   $$\gamma\le\Gamma_\lambda:=\frac{\lambda+5/6}{1+\lambda}.$$
--
--   This is the general-slope form of Proposition 9.2. As in the proof on p.41, if $b_1\le\Gamma_\lambda$ the first inverse coefficient suffices. Otherwise the affine strip makes $b_3>0$, and truncating the inverse majorant after its linear and cubic terms gives a contradiction at $\Gamma_\lambda$. For $\lambda=1$ this specializes exactly to $\gamma\le11/12$.
-- source:
--   Saha, Li, Xue, Chaudhuri, Klivans, Kothari, Meka, New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158, Proposition 9.2 and its proof, p.41; general one-parameter affine family and barrier in Li et al., arXiv:2608.11195v3, Appendix A, pp.16-17 (Second intervention: the general bound, through theory).

import Mathlib
import Definitions.Def_GrothendieckLB_IsAdmissible
import Definitions.Def_GrothendieckLB_taylorCoeff
open Topology

namespace GrothendieckLB

/-- Generalized Proposition 9.2: an affine strip of slope `1 + λ` forces every admissible inverse-majorant value to be at most `(λ + 5/6)/(1 + λ)`. -/
theorem majorant_barrier (lam : ℝ) (hlam : 1 / 2 ≤ lam) {H : ℝ → ℝ}
    (hodd : ∀ᶠ t in 𝓝 (0 : ℝ), H (-t) = -H t)
    (han : AnalyticAt ℝ H 0) (hb₁ : 0 < taylorCoeff 1 H) (hb₁' : taylorCoeff 1 H ≤ 1)
    (hb₃ : (1 + lam) * taylorCoeff 1 H - (lam + 5 / 6) ≤ taylorCoeff 3 H)
    {γ : ℝ} (hγ : IsAdmissible H γ) :
    γ ≤ (lam + 5 / 6) / (1 + lam) := by sorry
