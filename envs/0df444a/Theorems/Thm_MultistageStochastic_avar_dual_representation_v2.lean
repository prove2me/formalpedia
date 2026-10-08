-- Prove2me | Theorems.Thm_MultistageStochastic_avar_dual_representation_v2
-- name    : MultistageStochastic.avar_dual_representation_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:07.478888+00:00
-- url     : https://prove2.me/theorems/0f1c92c5-d3bb-4149-8435-e7bc2a65ddb4
-- title:
--   Corollary 3.18 — the dual representations (3.18) and (3.19) of the Average Value-at-Risk, with (3.18) corrected by the constraint $Z\ge0$
-- statement:
--   Let $Y\in L^\infty$ on a probability space and $\alpha\in[0,1]$. For $\alpha<1$,
--   $$\mathsf{AV@R}_\alpha(Y)=\sup\Bigl\{\mathbb E(YZ)\ \Big|\ \mathbb E(Z)=1,\ Z\ge0,\ \mathsf{AV@R}_p(Z)\le\tfrac1{1-\alpha}\text{ for all }p\in[\alpha,1]\Bigr\}\tag{3.18, corrected}$$
--   and
--   $$\mathsf{AV@R}_\alpha(Y)=\sup\Bigl\{\mathbb E(YZ)\ \Big|\ \mathbb EZ=1,\ 0\le Z,\ Z\le\tfrac1{1-\alpha}\Bigr\},\tag{3.19}$$
--   the suprema over integrable $Z$; and for $\alpha=1$ the second representation reads $\operatorname{ess\,sup}Y=\sup\{\mathbb E(YZ)\mid\mathbb EZ=1,\ 0\le Z\}$.
--
--   This is Corollary 3.18, the specialisation of the dual representation (3.15)–(3.16) of distortion risk functionals to $\sigma_\alpha=(1-\alpha)^{-1}\mathbf 1_{[\alpha,1)}$. The point the source makes is that the constraints of (3.15) collapse: only the levels in $[\alpha,1]$ matter, and they are equivalent to the pointwise bound $0\le Z\le1/(1-\alpha)$, which recovers formula (3.4).
--
--   **Formalization Note.** The printed (3.18) carries no sign constraint on $Z$. In the general constraint set (3.16) the inequalities $\mathsf{AV@R}_p(Z)\le(1-p)^{-1}\int_p^1\sigma_\alpha$ at the levels $p<\alpha$ read $\int_0^p\mathsf{V@R}_u(Z)\,du\ge0$ and force $Z\ge0$ a.s.; restricting the levels to $[\alpha,1]$ silently discards this, and the printed (3.18) is false: a $Z$ negative on a set of small probability satisfies $\mathbb EZ=1$ and the $[\alpha,1]$ constraints while $\mathbb E(YZ)>\mathsf{AV@R}_\alpha(Y)$ (accepted disproof on a two-point space, which works equally on an atomless space). The retired formal statement transcribed (3.18) faithfully, so the fault is in the source (A1); this version states the corrected (3.18), with $0\le Z$ a.s. restored — equivalently, the constraints of (3.16) at all levels $p\in[0,1)$ kept — and leaves (3.19) and the case $\alpha=1$ unchanged. As before, in (3.18) the constraint is stated for $p\in[\alpha,1]$ including $p=1$, where the Average Value-at-Risk is the essential supremum; in (3.19) the source writes $\alpha\le1$ with $1/(1-\alpha)=+\infty$ at $\alpha=1$, and that case is stated separately with the upper bound dropped since $1/(1-1)$ is $0$ in Lean. The suprema are over the subtype of integrable $Z$ satisfying the constraints; each family is nonempty ($Z\equiv1$) and bounded ($|\mathbb E(YZ)|\le\|Y\|_\infty$ as $Z\ge0$, $\mathbb EZ=1$), so no junk value of a real supremum is involved. Pointwise constraints on $Z$ hold almost surely.
-- source:
--   Georg Ch. Pflug and Alois Pichler, Multistage Stochastic Optimization, Springer 2014, https://doi.org/10.1007/978-3-319-08843-3 — Section 3.3.2, printed pp. 107–108 (PDF pp. 120–121), Corollary 3.18, formulas (3.18) and (3.19) — corrected transcription of (3.18): the constraint 0 ≤ Z, imposed by the general representation (3.15)–(3.16) through the levels p < α and dropped in the printed corollary, is restored

import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_MultistageStochastic_Distortion
open MeasureTheory
open scoped ENNReal

namespace MultistageStochastic

/-- Pflug & Pichler, *Multistage Stochastic Optimization*, §3.3.2, Corollary 3.18, the dual
representations (3.18) and (3.19) of the Average Value-at-Risk, with (3.18) **corrected**: the
printed (3.18) keeps from the general constraint set (3.16) of Theorem 3.16 only the levels
`p ∈ [α, 1]`, and thereby drops the constraints at the levels `p < α`, which force `Z ≥ 0`;
without `Z ≥ 0` the printed (3.18) is false (a density negative on a set of small probability is
admissible and `E(YZ)` exceeds `AV@R_α(Y)`). The corrected (3.18) restores `0 ≤ Z` a.s.; (3.19)
is as printed. -/
theorem avar_dual_representation_v2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : MemLinfty P Y) (α : ℝ) (hα : 0 ≤ α) :
    (α < 1 →
      averageValueAtRisk P Y α
        = ⨆ Z : {Z : Ω → ℝ // Integrable Z P ∧ ∫ ω, Z ω ∂P = 1 ∧ (∀ᵐ ω ∂P, 0 ≤ Z ω) ∧
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
