-- Prove2me | Theorems.Thm_MultistageStochastic_distortion_inf_representation
-- name    : MultistageStochastic.distortion_inf_representation
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-23T20:25:35.790031+00:00
-- url     : https://prove2.me/theorems/db010e9a-ba22-4d7f-b652-2ff81aa4c2aa
-- title:
--   Theorem 3.22 — R_σ(Y) is the infimum of E(h(Y)) over h with ∫ h*(σ(u)) du ≤ 0
-- statement:
--   Let $\sigma$ be a distortion function and $Y\in L^\infty$ on a probability space. Then
--
--   $$
--   \mathcal R_\sigma(Y)\;=\;\inf\Bigl\{\mathbb E\bigl(h(Y)\bigr)\ :\ \int_0^1h^*(\sigma(u))\,du\le 0\Bigr\} ,
--   \tag{3.24}
--   $$
--
--   the infimum over measurable $h:\mathbb R\to\mathbb R$, where $h^*(s)=\sup_y\,(s\,y-h(y))$ is the
--   conjugate of $h$.
--
--   This is Theorem 3.22, the "alternative description" of Section 3.4: it expresses a distortion
--   functional as an infimum instead of the supremum of (3.15), so that a stochastic program with a
--   risk-functional objective becomes a joint minimisation over the decision and over $h$, as (3.3)
--   does for the Average Value-at-Risk with $h(y)=q+\frac{1}{1-\alpha}(y-q)_+$. For that special
--   case the infimum over $h$ collapses to an infimum over the scalar $q$.
--
--   **Formalization Note** An admissible $h$ is measurable, has $h^*(\sigma(u))$ finite for almost
--   every level, $u\mapsto h^*(\sigma(u))$ integrable on $(0,1)$ with integral at most $0$, and
--   $h(Y)$ integrable; these are the conditions under which the two expectations in (3.24) are the
--   integrals the source intends, and without them Lean's integral of a non-integrable function is
--   $0$, which would let a meaningless $h$ into the constraint set. The conjugate is valued in the
--   extended reals, so a supremum equal to $+\infty$ is recorded as such rather than replaced by a
--   junk real. The infimum is over the subtype of admissible $h$; the source's identity presupposes
--   that this set is nonempty, and the proof exhibits admissible $h$ with $\mathbb E(h(Y))$ close to
--   $\mathcal R_\sigma(Y)$.
-- source:
--   Georg Ch. Pflug and Alois Pichler, Multistage Stochastic Optimization, Springer 2014, https://doi.org/10.1007/978-3-319-08843-3 — Section 3.4, printed p. 111 (PDF p. 124), Theorem 3.22: "The distortion risk functional R_σ has the representation R_σ(Y) = inf{E(h(Y)) : ∫_0^1 h*(σ(u)) du ≤ 0}, (3.24) where the infimum is among all measurable functions h : R → R", with h*(σ) = sup_{y∈R} σ·y − h(y) in footnote 6.

import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_MultistageStochastic_Distortion
open MeasureTheory
open scoped ENNReal

namespace MultistageStochastic
theorem distortion_inf_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℝ → ℝ) (hσ : IsDistortionFunction σ)
    (Y : Ω → ℝ) (hY : MemLinfty P Y) :
    distortionFunctional P σ Y
      = ⨅ h : {h : ℝ → ℝ // IsAdmissibleConjugate σ h ∧ Integrable (fun ω => h (Y ω)) P},
          ∫ ω, (h : ℝ → ℝ) (Y ω) ∂P := by sorry
end MultistageStochastic
