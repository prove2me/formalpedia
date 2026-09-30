-- Prove2me | Theorems.Thm_MultistageStochastic_distortion_dual_representation
-- name    : MultistageStochastic.distortion_dual_representation
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:26:57.266315+00:00
-- url     : https://prove2.me/theorems/c6de78f1-4979-4fc8-93f8-69f3c0887b20
-- title:
--   Theorem 3.16 — the dual representation (3.15) of distortion risk functionals
-- statement:
--   Let $\sigma$ be a distortion function — nonnegative, nondecreasing on $[0,1)$, integrating to
--   $1$ — on a probability space $(\Omega,\mathcal F,P)$, and let $Y\in L^\infty$. Then
--
--   $$
--   \mathcal R_\sigma(Y)\;=\;\sup\Bigl\{\mathbb E(Y\cdot Z)\ \Big|\ \mathbb E(Z)=1,\ \text{and }
--   \mathsf{AV@R}_\alpha(Z)\le\frac{1}{1-\alpha}\int_\alpha^1\sigma(u)\,du\text{ for all }\alpha\in[0,1)\Bigr\} ,
--   \tag{3.15}
--   $$
--
--   the supremum over integrable $Z$. The constraint set is the relation $Z\preccurlyeq\sigma$ of
--   (3.16), and the theorem says that the distortion functional is the support function of that
--   set: $\mathcal R_\sigma(Y)=\sup_{Z\preccurlyeq\sigma}\mathbb E(YZ)$, the Fenchel–Moreau
--   representation with conjugate $\mathcal R_\sigma^*$ equal to $0$ on $\{Z\preccurlyeq\sigma\}$ and
--   $+\infty$ elsewhere (Remark 3.17).
--
--   This is Theorem 3.16, the dual representation from which the source derives the dual
--   characterisation of the Average Value-at-Risk (Corollary 3.18), the co-monotone maximum
--   (Corollary 3.19) and, together with Kusuoka's theorem, the dual representation of every version
--   independent risk functional (Corollary 3.21). The content is the identification of the
--   conjugate: by the rearrangement (Chebyshev) inequality $\mathbb E(YZ)\le\int_0^1G_Y^{-1}G_Z^{-1}$,
--   so $\mathcal R_\sigma^*(Z)=\sup_Y\int_0^1G_Y^{-1}(u)\,(G_Z^{-1}(u)-\sigma(u))\,du$, and testing
--   with indicator-type $Y$ shows this is $0$ exactly when the upper-tail averages of $Z$ are
--   dominated by those of $\sigma$.
--
--   **Formalization Note** The source writes the constraint for $\alpha\in[0,1]$. At $\alpha=1$ the
--   right-hand side is $\frac{1}{0}\int_1^1\sigma$, to be read as the limit $\sigma(1^-)$; since the
--   Average Value-at-Risk is continuous and nondecreasing in its level, the $\alpha=1$ constraint is
--   the limit of the $\alpha<1$ ones and is implied by them, so the formal constraint set quantifies
--   over $[0,1)$, where every term is finite and no division by zero occurs. The supremum is a real
--   supremum over a nonempty ($Z\equiv 1$ is feasible, as the average of $\sigma$ over $[\alpha,1]$ is
--   at least $1$) and bounded family ($Z\ge 0$ follows from the constraints, so
--   $\mathbb E(YZ)\le\|Y\|_\infty$), so it is not a junk value. No atomless hypothesis is imposed,
--   matching the printed statement; the identity holds on atomic spaces as well, as the two-point
--   instances in the mission notes verify.
-- source:
--   Georg Ch. Pflug and Alois Pichler, Multistage Stochastic Optimization, Springer 2014, https://doi.org/10.1007/978-3-319-08843-3 — Section 3.3.2, printed pp. 105-106 (PDF pp. 118-119), Theorem 3.16 (Dual Representation of Distortion Risk Functionals): "Let R_σ be a distortion risk functional. Then R_σ has the representation R_σ(Y) = sup{E(Y·Z) | E(Z) = 1, and AV@R_α(Z) ≤ (1/(1−α)) ∫_α^1 σ(u) du for all α ∈ [0, 1]}. (3.15)"

import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_MultistageStochastic_Distortion
open MeasureTheory
open scoped ENNReal

namespace MultistageStochastic
theorem distortion_dual_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℝ → ℝ) (hσ : IsDistortionFunction σ)
    (Y : Ω → ℝ) (hY : MemLinfty P Y) :
    distortionFunctional P σ Y
      = ⨆ Z : {Z : Ω → ℝ // DominatedByDistortion P σ Z},
          ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P := by sorry
end MultistageStochastic
