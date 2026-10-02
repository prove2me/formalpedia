-- Prove2me | Theorems.Thm_MultistageStochastic_avar_dual_representation
-- name    : MultistageStochastic.avar_dual_representation
-- status  : Disproved
-- author  : @naimengye
-- created : 2026-09-23T20:24:15.661564+00:00
-- url     : https://prove2.me/theorems/a338a384-59bf-4f87-b317-ee60761f1c9c
-- title:
--   Corollary 3.18 — the dual representations (3.18) and (3.19) of the Average Value-at-Risk
-- statement:
--   Let $Y\in L^\infty$ on a probability space and $\alpha\in[0,1]$. For $\alpha<1$,
--
--   $$
--   \mathsf{AV@R}_\alpha(Y)\;=\;\sup\Bigl\{\mathbb E(YZ)\ \Big|\ \mathbb E(Z)=1,\ \mathsf{AV@R}_p(Z)\le\tfrac{1}{1-\alpha}\text{ for all }p\in[\alpha,1]\Bigr\}
--   \tag{3.18}
--   $$
--
--   and
--
--   $$
--   \mathsf{AV@R}_\alpha(Y)\;=\;\sup\Bigl\{\mathbb E(YZ)\ \Big|\ \mathbb E Z=1,\ 0\le Z,\ Z\le\tfrac{1}{1-\alpha}\Bigr\} ,
--   \tag{3.19}
--   $$
--
--   the suprema over integrable $Z$; and for $\alpha=1$ the second representation reads
--   $\operatorname{ess\,sup}Y=\sup\{\mathbb E(YZ)\mid\mathbb EZ=1,\ 0\le Z\}$.
--
--   This is Corollary 3.18, the specialisation of the dual representation of distortion risk
--   functionals to $\sigma_\alpha=(1-\alpha)^{-1}\mathbf 1_{[\alpha,1)}$. The point the source makes
--   is that the constraints of (3.15) collapse: only the levels in $[\alpha,1]$ matter, and they are
--   equivalent to the pointwise bound $0\le Z\le 1/(1-\alpha)$, which recovers formula (3.4).
--
--   **Formalization Note** In (3.18) the constraint is stated for $p\in[\alpha,1]$ including
--   $p=1$, where the Average Value-at-Risk is the essential supremum, exactly as printed. In (3.19)
--   the source writes $\alpha\le 1$ with $1/(1-\alpha)=+\infty$ at $\alpha=1$; that case is stated
--   separately with the upper bound dropped, since $1/(1-1)$ is $0$ in Lean and would make the
--   constraint set empty. The suprema are over the subtype of integrable $Z$ satisfying the
--   constraints; each family is nonempty ($Z\equiv 1$) and bounded ($|\mathbb E(YZ)|\le\|Y\|_\infty$
--   as $Z\ge 0$, $\mathbb EZ=1$), so no junk value of a real supremum is involved. Pointwise
--   constraints on $Z$ hold almost surely.
-- source:
--   Georg Ch. Pflug and Alois Pichler, Multistage Stochastic Optimization, Springer 2014, https://doi.org/10.1007/978-3-319-08843-3 — Section 3.3.2, printed pp. 107-108 (PDF pp. 120-121), Corollary 3.18: "The Average Value-at-Risk at level α has the equivalent representations AV@R_α(Y) = sup{E(YZ) | E(Z) = 1, AV@R_p(Z) ≤ 1/(1−α) for all p ∈ [α, 1]} (α < 1) (3.18) and AV@R_α(Y) = sup{E(YZ) | EZ = 1, 0 ≤ Z, Z ≤ 1/(1−α)} (α ≤ 1). (3.19)"

import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_MultistageStochastic_Distortion
open MeasureTheory
open scoped ENNReal

namespace MultistageStochastic
theorem avar_dual_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : MemLinfty P Y) (α : ℝ) (hα : 0 ≤ α) :
    (α < 1 →
      averageValueAtRisk P Y α
        = ⨆ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧
            ∀ p : ℝ, α ≤ p → p ≤ 1 → averageValueAtRisk P Z p ≤ (1 - α)⁻¹},
            ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P) ∧
    (α < 1 →
      averageValueAtRisk P Y α
        = ⨆ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧
            ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ (1 - α)⁻¹},
            ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P) ∧
    (α = 1 →
      averageValueAtRisk P Y α
        = ⨆ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧ ∀ᵐ ω ∂P, 0 ≤ Z ω},
            ∫ ω, Y ω * (Z : Ω → ℝ) ω ∂P) := by sorry
end MultistageStochastic
