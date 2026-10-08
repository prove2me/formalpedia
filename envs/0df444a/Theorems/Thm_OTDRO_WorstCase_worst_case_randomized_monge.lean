-- Prove2me | Theorems.Thm_OTDRO_WorstCase_worst_case_randomized_monge
-- name    : OTDRO.WorstCase.worst_case_randomized_monge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:10.99805+00:00
-- url     : https://prove2.me/theorems/86b7457b-e49d-4324-9e5c-6b9e113099f9
-- title:
--   Theorem 6(c), p. 14 — if λ*(β) > λ_thr(β), the law of X + √δ G A(X)⁻¹β, G = ZG₋ + (1 − Z)G₊, attains the worst case with E[c(X, X*)] = δ
-- statement:
--   Assume Assumptions 1 and 2, $\delta>0$ and $B\subseteq\mathbb R^d$ convex; fix $\beta\in B$ with $\beta\neq0$ and a dual optimizer $\lambda_*(\beta)\in\arg\min_{\lambda\ge0}f_\delta(\beta,\lambda)$. Suppose $\lambda_*(\beta)>\lambda_{thr}(\beta)$. Then there are measurable functions $G_-,G_+:\mathbb R^d\to\mathbb R$ such that, for $P_0$-almost every $x$, $G_-(x)$ and $G_+(x)$ belong to $\Gamma^*(\beta,\lambda_*(\beta);x)$ and
--   $$G_-(x)^2=\min_{g\in\Gamma^*(\beta,\lambda_*(\beta);x)}g^2,\qquad G_+(x)^2=\max_{g\in\Gamma^*(\beta,\lambda_*(\beta);x)}g^2 ;$$
--   the moments $\bar c=E_{P_0}[G_+^2\beta^{\mathsf T}A(X)^{-1}\beta]$ and $\underline c=E_{P_0}[G_-^2\beta^{\mathsf T}A(X)^{-1}\beta]$ are finite; $q=(\bar c-1)/(\bar c-\underline c)$ lies in $[0,1]$; and, with $Z$ a Bernoulli$(q)$ variable independent of $X\sim P_0$, $G=ZG_-(X)+(1-Z)G_+(X)$ and
--   $$X^*=X+\sqrt\delta\,G\,A(X)^{-1}\beta,$$
--   the joint law $\pi^*$ of $(X,X^*)$ satisfies $E[c(X,X^*)]=\delta$ and attains the worst case:
--   $$E_{\pi^*}\bigl[\ell(\beta^{\mathsf T}X^*)\bigr]=\sup_{P:\,D_c(P_0,P)\le\delta}E_P\bigl[\ell(\beta^{\mathsf T}X)\bigr].$$
--
--   The theorem describes an adversarial distribution explicitly: each data point is moved along the single direction $A(x)^{-1}\beta$ by an amount read off the one-dimensional problem (7), randomizing between two extreme maximizers only to spend the transport budget exactly.
--
--   **Formalization Note** The page defines $G_-=\inf\Gamma(\beta,\lambda_*(\beta);X)$ and $G_+=\sup\Gamma(\beta,\lambda_*(\beta);X)$ (with $\Gamma$ for $\Gamma^*$). Its proof (p. 40) instead takes measurable selections with $g_+^2=\sup_{g\in\Gamma^*}g^2$ and $g_-^2=\inf_{g\in\Gamma^*}g^2$, and only that choice makes $\underline c\le1\le\bar c$ follow from the first-order conditions. With the printed choice the statement can fail: for $d=1$, $A\equiv1$, $\delta=1$, $\beta=1$, $\ell(u)=\max(-3u,u,3u-c_0)$ with $c_0$ large and $P_0$ uniform on two suitable points, $\lambda_*=1$ is a dual optimizer with $\Gamma^*=\{-3/2,1/2\}$ at one point and $\{1/2,3/2\}$ at the other, so the printed $\bar c=\underline c=5/4$ and no mixture has cost $\delta$. The statement follows the proof. "The law of $X^*$ attains the supremum in (6)" is encoded with the published primal problem of Blanchet–Murthy: $\pi^*$ is a coupling with first marginal $P_0$ and cost at most $\delta$ (`primalFeasible`) whose value $\int\ell(\beta^{\mathsf T}y)\,d\pi^*$ equals the supremum `primalValue` over all such couplings; the cost is the lower Lebesgue integral of $c$. The random $Z$ is encoded through the mixture law (`mixtureCoupling`). The convexity of $B$ is the paper's standing assumption (p. 1).
-- source:
--   arXiv:1810.02403v3, Theorem 6(c), p. 14, (10); proof §5.4, pp. 39–40

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_primalFeasible
import Definitions.Def_ModelRiskOT_Duality_primalValue
import Definitions.Def_OTDRO_Dual_Setting
import Definitions.Def_OTDRO_WorstCase_Transport

open MeasureTheory

namespace OTDRO.WorstCase

/-- **Theorem 6(c)** (arXiv:1810.02403v3, p. 14; proof §5.4, pp. 39–40). Under Assumptions 1–2,
for `β ≠ 0` and a dual optimizer `λ*(β) > λ_thr(β)`, there are measurable selections `G₋, G₊` of
`Γ*(β, λ*(β); ·)` such that, with `c̄ = E[G₊² βᵀA⁻¹β]`, `c̲ = E[G₋² βᵀA⁻¹β]` and
`q = (c̄ − 1)/(c̄ − c̲) ∈ [0, 1]`, the joint law of `(X, X*)`,
`X* = X + √δ (Z G₋ + (1 − Z) G₊) A(X)⁻¹β` with `Z ∼ Bernoulli(q)` independent of `X`, is a
feasible coupling that attains the worst-case value and has transport cost exactly `δ`.
`G₋, G₊` are the elements of `Γ*` of least and greatest square, as in the proof (p. 40). -/
theorem worst_case_randomized_monge {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0] (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax) (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B) (hβ : β ≠ 0)
    (lamStar : ℝ) (hlam0 : 0 ≤ lamStar)
    (hmin : IsMinOn (fun l => OTDRO.Dual.fDelta P0 ℓ A δ β l) (Set.Ici 0) lamStar)
    (hthr : OTDRO.Dual.lamThr P0 ℓ A δ β < lamStar) :
    ∃ Gminus Gplus : EuclideanSpace ℝ (Fin d) → ℝ,
      AEMeasurable Gminus P0 ∧ AEMeasurable Gplus P0 ∧
      (∀ᵐ x ∂P0, Gminus x ∈ OTDRO.Dual.maximizers ℓ A δ β lamStar x ∧
        Gplus x ∈ OTDRO.Dual.maximizers ℓ A δ β lamStar x ∧
        ∀ g ∈ OTDRO.Dual.maximizers ℓ A δ β lamStar x, Gminus x ^ 2 ≤ g ^ 2 ∧ g ^ 2 ≤ Gplus x ^ 2) ∧
      Integrable (fun x => Gminus x ^ 2 * OTDRO.Dual.quadInv A β x) P0 ∧
      Integrable (fun x => Gplus x ^ 2 * OTDRO.Dual.quadInv A β x) P0 ∧
      0 ≤ bernoulliWeight (sqMoment P0 A β Gplus) (sqMoment P0 A β Gminus) ∧
      bernoulliWeight (sqMoment P0 A β Gplus) (sqMoment P0 A β Gminus) ≤ 1 ∧
      mixtureCoupling P0 A δ β Gminus Gplus ∈
        ModelRiskOT.Duality.primalFeasible (OTDRO.Dual.mahalCost A) P0 δ ∧
      ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x))
          (mixtureCoupling P0 A δ β Gminus Gplus) =
        ModelRiskOT.Duality.primalValue (OTDRO.Dual.mahalCost A) (fun x => ℓ (inner ℝ β x)) P0 δ ∧
      ∫⁻ p, ENNReal.ofReal (OTDRO.Dual.mahalCost A p.1 p.2) ∂(mixtureCoupling P0 A δ β Gminus Gplus) =
        ENNReal.ofReal δ := by sorry

end OTDRO.WorstCase
