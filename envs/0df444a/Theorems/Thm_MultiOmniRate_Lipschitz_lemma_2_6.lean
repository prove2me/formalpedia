-- Prove2me | Theorems.Thm_MultiOmniRate_Lipschitz_lemma_2_6
-- name    : MultiOmniRate.Lipschitz.lemma_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:22:35.192846+00:00
-- url     : https://prove2.me/theorems/3e63fb58-d914-4353-8930-6d6ab367f21b
-- title:
--   Lemma 2.6 — the Bayes risk is concave, bounded by $1$, $1$-Lipschitz in $\ell_1$, with supergradient $\Delta\ell^{\mathrm{pr}}(p)$
-- statement:
--   Let $\ell:\mathcal A\times\mathcal Y\to[-1,1]$ be a loss with a best response $\mathrm{BR}_\ell(p)\in\arg\min_a\mathbb E_{y\sim p}\ell(a,y)$ for every $p\in\Delta_K$, and let $L_\ell(p')=\min_{a}\mathbb E_{y\sim p'}\ell(a,y)$ be its Bayes risk. Then $L_\ell$ is concave on $\Delta_K$, and for all $p,p'\in\Delta_K$
--   $$|L_\ell(p)|\le1,\qquad |L_\ell(p')-L_\ell(p)|\le\|p'-p\|_1,\qquad L_\ell(p')\le L_\ell(p)+\langle\Delta\ell^{\mathrm{pr}}(p),\,p'-p\rangle\quad(2.5),$$
--   where $\Delta\ell^{\mathrm{pr}}(p)=(\ell(\mathrm{BR}_\ell(p),y)-\ell(\mathrm{BR}_\ell(p),0))_{y}$. Thus $\Delta\ell^{\mathrm{pr}}(p)$ is a supergradient of the Bayes risk at $p$.
--
--   These are the geometric facts behind the covering bounds for the decision weights.
--
--   Differences from the source:
--   - encoding: labels $\mathcal Y=\{0,\dots,K-1\}$ → `Fin K`, with `[NeZero K]` (implied by $K\ge2$) so that label $0$ exists; reason: relabeling; same instances
--   - generalization: bounded loss with a fixed *measurable* best response → any `BRLoss` (bounded loss with a best response), no measurability; reason: Lemma 2.6 is pointwise; the paper's losses are the measurable special case
--   - encoding: $L_\ell=\min_a\mathbb E_{y\sim p'}\ell(a,y)$ on $\Delta_K$ → `bayesRisk ℓ.loss`, the infimum over actions, defined on all of $\mathbb R^K$; every clause is stated for points of $\Delta_K$ (concavity as `ConcaveOn ℝ (stdSimplex ℝ (Fin K))`); reason: same values on $\Delta_K$, where the minimum is attained at the best response
--   - reading: "Thus $\Delta\ell^{pr}(p)$ is a supergradient of the Bayes risk at $p$" → the inequality (2.5) for all $p,p'\in\Delta_K$; reason: the sentence restates (2.5)
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), p. 23, Lemma 2.6

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MultiOmniRate.Lipschitz

theorem lemma_2_6 {K : ℕ} [NeZero K] (hK : 2 ≤ K) {A : Type*} (ℓ : BRLoss K A) :
    ConcaveOn ℝ (stdSimplex ℝ (Fin K)) (bayesRisk ℓ.loss) ∧
    (∀ p ∈ stdSimplex ℝ (Fin K), |bayesRisk ℓ.loss p| ≤ 1) ∧
    (∀ p ∈ stdSimplex ℝ (Fin K), ∀ p' ∈ stdSimplex ℝ (Fin K),
      |bayesRisk ℓ.loss p' - bayesRisk ℓ.loss p| ≤ l1 (p' - p)) ∧
    (∀ (p : Simplex K), ∀ p' ∈ stdSimplex ℝ (Fin K),
      bayesRisk ℓ.loss p' ≤ bayesRisk ℓ.loss p + dot (dLoss (ℓ.pr p)) (p' - (p : Fin K → ℝ))) := by sorry

end MultiOmniRate.Lipschitz
