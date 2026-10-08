-- Prove2me | Theorems.Thm_ManyServerFluid_Uniqueness_remark_4_3
-- name    : ManyServerFluid.Uniqueness.remark_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:55.174976+00:00
-- url     : https://prove2.me/theorems/62389cad-1bea-40d1-b133-ff25dd91e6b9
-- title:
--   Remark 4.3, (4.4) — integration by parts for ∫_[0,t] f(t−s)(1−G(t−s)) dZ(s)
-- statement:
--   Let $Z \in BV_0[0,\infty)$ be a càdlàg function of bounded variation on bounded intervals with $Z(0) = 0$, let $f \in \mathcal C_b^1(\mathbb R_+)$ and $t \ge 0$. Then
--   $$\int_{[0,t]} f(t-s)\big(1-G(t-s)\big)\,dZ(s) = f(0)Z(t) + \int_{[0,t]} f'(t-s)\big(1-G(t-s)\big)Z(s)\,ds - \int_{[0,t]} f(t-s)\,g(t-s)\,Z(s)\,ds.$$
--
--   This rewrites the Stieltjes term of the representation (4.3) through $Z$ itself rather than $dZ$; it is what makes the term continuous in $Z$ for the supremum norm, and so drives Lemma 4.5 and Theorem 4.6.
--
--   **Formalization Note.** $Z$ is $Z_1 - Z_2$ with $Z_1, Z_2 \in \mathcal I_0[0,\infty)$ and $dZ = dZ_1 - dZ_2$; $f$ is a $C^1$ function on $\mathbb R$ with $f, f'$ bounded on $[0,\infty)$ (a $\mathcal C_b^1(\mathbb R_+)$ function, one-sided at $0$, extends to one).
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 52, Remark 4.3, (4.4)

import Mathlib
import Definitions.Def_ManyServerFluid_Uniqueness_Model
import Definitions.Def_ManyServerFluid_Uniqueness_AgeEquation
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace ManyServerFluid.Uniqueness

/-- Remark 4.3, (4.4), p. 52: for Z = Z₁ − Z₂ ∈ BV_0[0, ∞), f ∈ C_b^1(R₊) and t ≥ 0,
∫_[0,t] f(t − s)(1 − G(t − s)) dZ(s)
  = f(0)Z(t) + ∫_[0,t] f′(t − s)(1 − G(t − s)) Z(s) ds − ∫_[0,t] f(t − s) g(t − s) Z(s) ds. -/
theorem remark_4_3 (S : ServiceLaw) (Z₁ Z₂ : ℝ → ℝ) (hZ₁ : ServiceLaw.IsI0 Z₁)
    (hZ₂ : ServiceLaw.IsI0 Z₂) (f : ℝ → ℝ) (hf : IsCb1 f) (t : ℝ) (ht : 0 ≤ t) :
    bvInt Z₁ Z₂ (Icc 0 t) (fun s => f (t - s) * (1 - S.G (t - s))) =
      f 0 * (Z₁ t - Z₂ t)
      + ∫ s in Icc 0 t, deriv f (t - s) * (1 - S.G (t - s)) * (Z₁ s - Z₂ s)
      - ∫ s in Icc 0 t, f (t - s) * S.g (t - s) * (Z₁ s - Z₂ s) := by sorry

end ManyServerFluid.Uniqueness
