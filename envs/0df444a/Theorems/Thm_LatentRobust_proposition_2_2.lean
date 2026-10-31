-- Prove2me | Theorems.Thm_LatentRobust_proposition_2_2
-- name    : LatentRobust.proposition_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:41.61781+00:00
-- url     : https://prove2.me/theorems/439c32fd-3646-455c-b5ac-357f707e5475
-- title:
--   Proposition 2.2 — the Bayes classifier $\operatorname{sign}(\eta-1/2)$ has the lowest standard risk
-- statement:
--   Let $P$ be a probability law of a pair $(x,y)$ with $x\in\mathbb R^d$ and $y\in\{+1,-1\}$, let $P_X$ be the law of $x$, and let $\eta(x)=P(y=+1\mid X=x)$ be the regression function: a measurable function with values in $[0,1]$ such that
--   $$
--   P(x\in A,\ y=+1)=\int_A \eta\,dP_X\qquad\text{for every Borel set }A\subseteq\mathbb R^d .
--   $$
--   Then for every Borel classifier $h:\mathbb R^d\to\{+1,-1\}$,
--   $$
--   \mathrm{SR}\big(h_{\mathrm{Bayes}}\big)\le \mathrm{SR}(h),\qquad h_{\mathrm{Bayes}}(x)=\operatorname{sign}\big(\eta(x)-\tfrac12\big),
--   $$
--   where $\mathrm{SR}(h)=P(h(x)y\le0)$ is the standard risk.
--
--   This is the justification for calling $h_{\mathrm{Bayes}}$ Bayes-optimal; Corollary 2.3 applies it to the two latent models.
--
--   **Formalization Note** The statement holds for every version $\eta$ of the conditional probability.
--
--   Differences from the source:
--   - reading: sign(·) with values in {+1, −1}, ties to −1 (p.7 gives +1 when +1 has the higher likelihood, p.19 gives the negative label on {η ≤ 1/2}) → sgn t = +1 for t > 0 and −1 for t ≤ 0; reason: a {±1}-valued classifier needs a value at 0, and this is the page's tie; Real.sign would give 0
--   - encoding: η(x) := P(y = +1 | X = x) → any measurable η : ℝ^d → [0, 1] with P(A × {+1}) = ∫_A η dP_X for every Borel A; reason: these are exactly the versions of the conditional probability; the conclusion holds for each
--   - encoding: a joint law of (x, y) with y ∈ {+1, −1} → a probability measure on ℝ^d × ℝ whose labels are +1 or −1 almost surely; reason: same laws
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, Proposition 2.2, p.7 (proof A.1, p.19)

import Mathlib
import Definitions.Def_LatentRobust_sgn
import Definitions.Def_LatentRobust_boundaryRisk

namespace LatentRobust

open MeasureTheory

/-- **Proposition 2.2** (Javanmard, Mehrabi, arXiv:2110.11950v2, §2.3, p.7): among all Borel classifiers
`h : ℝ^d → {+1, −1}`, the Bayes-optimal classifier `h_Bayes(x) = sign(η(x) − 1/2)` has the
lowest standard risk, where `η(x) = P(y = +1 | X = x)`.

**Formalization Note** `P` is any probability law of `(x, y)` on `ℝ^d × ℝ` whose labels are
`±1` almost surely. `η` is any version of the regression function: a measurable
`[0, 1]`-valued function with `P(A × {+1}) = ∫_A η dP_X` for every Borel `A`, `P_X` the law
of `x`. The conclusion holds for every such version. `sign` is `sgn` (`sgn 0 = −1`). -/
theorem proposition_2_2 {d : ℕ} (P : Measure ((Fin d → ℝ) × ℝ)) [IsProbabilityMeasure P]
    (hlabel : ∀ᵐ xy ∂P, xy.2 = 1 ∨ xy.2 = -1)
    (η : (Fin d → ℝ) → ℝ) (hη_meas : Measurable η) (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (hη : ∀ A : Set (Fin d → ℝ), MeasurableSet A →
      P (A ×ˢ {(1 : ℝ)}) = ∫⁻ x in A, ENNReal.ofReal (η x) ∂(P.map Prod.fst))
    (h : (Fin d → ℝ) → ℝ) (hh_meas : Measurable h) (hh : ∀ x, h x = 1 ∨ h x = -1) :
    standardRisk P (fun x => sgn (η x - 1 / 2)) ≤ standardRisk P h := by sorry

end LatentRobust
