-- Prove2me | Theorems.Thm_GMRDiversity_Supplement_theorem_1
-- name    : GMRDiversity.Supplement.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:10:08.527197+00:00
-- url     : https://prove2.me/theorems/9b969123-6a47-4ab1-9c12-187bf9d71a63
-- title:
--   Theorem 1 — Gaussian phase transition of $V^*_n$ in the drift $\alpha$
-- statement:
--   Let $\mathcal G$ be the one-dimensional Gaussian GMR framework: $X=\mathbb R$, $U(x)=x$, full feedback, generation $N(0,1)$, mutation $x\mapsto\mu x+\sigma_MZ$ and recombination $(x,y)\mapsto\lambda_1x+\lambda_2y+\sigma_RZ$ with fresh independent $Z\sim N(0,1)$, where $\mu,\lambda_1,\lambda_2\ge0$, $\sigma_M,\sigma_R>0$, and costs $c_G,c_M,c_R\in\mathbb N_{>0}$ are arbitrary. Let
--   $$
--   \alpha:=\min\Big\{1,\ \frac{1-\mu}{\sigma_M},\ \frac{1-\lambda_1-\lambda_2}{\sigma_R}\Big\}.
--   $$
--   Then, as $n\to\infty$ with all parameters fixed:
--
--   1. if $\alpha>0$, then $V^*_n(\mathcal G)=(1+o(1))\,\alpha^{-1}\sqrt{2\log n}$;
--   2. if $\alpha=0$, then $V^*_n(\mathcal G)=\Theta(n)$;
--   3. if $\alpha<0$, then $V^*_n(\mathcal G)=\exp(\Theta(n))$.
--
--   Here $V^*_n$ is the best expected maximum objective value over all adaptive randomized policies and horizons whose total cost is at most $n$ almost surely, and $\log$ is the natural logarithm.
--
--   The theorem separates contractive, averaging-type operators, which only reach the Gaussian extreme-value rate, from operators that preserve or amplify the parent value, which allow linear or exponential improvement.
--
--   **Formalization Note** $(1+o(1))a_n$ with $a_n=\alpha^{-1}\sqrt{2\log n}$ is stated as: for every $\varepsilon>0$, eventually $(1-\varepsilon)a_n\le V^*_n\le(1+\varepsilon)a_n$. $\Theta(n)$ and $\exp(\Theta(n))$ are two-sided bounds with constants $0<c\le C$ depending on the parameters, holding for all large $n$. $V^*_n$ is an extended-real supremum.
--
--   Differences from the source:
--   - encoding: V*_n(G) = (1 + o(1)) α^{−1}√(2 log n) → for every ε > 0, eventually (1 − ε)α^{−1}√(2 log n) ≤ V*_n ≤ (1 + ε)α^{−1}√(2 log n); reason: α^{−1}√(2 log n) > 0 for n ≥ 2, so this is V*_n / (α^{−1}√(2 log n)) → 1
--   - encoding: V*_n = Θ(n), V*_n = exp(Θ(n)) → ∃ c, C > 0, eventually c·n ≤ V*_n ≤ C·n, resp. exp(c·n) ≤ V*_n ≤ exp(C·n); reason: the definition of Θ as n → ∞ with fixed parameters; both halves are kept
--   - encoding: V^π_T = E[max_{t ≤ T} U(z_t)], V*_n a supremum → extended-real expectation E[max⁺] − E[max⁻] and EReal supremum, V^π_0 = −∞; reason: equals the usual expectation whenever it is defined (assumed on p.3) and avoids a junk real sSup
--   - encoding: policies in Π^obs_G (randomized, adaptive, any earlier indices) → Markov kernels from the full history of actions and candidates to actions, run law by Ionescu-Tulcea, an out-of-range index read as the latest round; reason: measurable behavioural policies with perfect recall induce the same laws as the paper's randomized policies, and the index convention only relabels legal actions
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), Theorem 1, p.6 (restated p.13; proof pp.13–15, display (7.1) p.13)

import Mathlib
import Definitions.Def_GMRDiversity_Supplement_value
import Definitions.Def_GMRDiversity_Supplement_gaussFramework

namespace GMRDiversity.Supplement

open MeasureTheory ProbabilityTheory Filter

/-- **Theorem 1 (one-dimensional Gaussian phase transition)** (Brandenberger, Doron-Arad, Mossel,
*Genetic Algorithms with Optimization Guided Operators*, STOC 2027 submission, manuscript sha256
f89f4f77…, Theorem 1, p.6; restated p.13, proof pp.13–15): for the Gaussian framework of §4 with
`µ, λ₁, λ₂ ≥ 0`, `σ_M, σ_R > 0` and any positive costs, let
`α := min{1, (1 − µ)/σ_M, (1 − λ₁ − λ₂)/σ_R}`. Then
* if `α > 0`, `V*_n(G) = (1 + o(1)) α⁻¹ √(2 log n)`;
* if `α = 0`, `V*_n(G) = Θ(n)`;
* if `α < 0`, `V*_n(G) = exp(Θ(n))`.

**Formalization Note.** All asymptotics are as `n → ∞` with the parameters fixed; the constants
may depend on them. `(1 + o(1)) a_n` with `a_n = α⁻¹√(2 log n) > 0` for `n ≥ 2` is stated as: for
every `ε > 0`, eventually `(1 − ε) a_n ≤ V*_n ≤ (1 + ε) a_n`. `Θ(n)` is `c n ≤ V*_n ≤ C n`
eventually, and `exp(Θ(n))` is `exp(c n) ≤ V*_n ≤ exp(C n)` eventually, with `c, C > 0`. `log` is
the natural logarithm. `V*_n` is the `EReal` supremum over all adaptive randomized policies and all
`T` with cost at most `n` almost surely. -/
theorem theorem_1 (μ l₁ l₂ σM σR : ℝ) (hμ : 0 ≤ μ) (hl₁ : 0 ≤ l₁) (hl₂ : 0 ≤ l₂) (hσM : 0 < σM)
    (hσR : 0 < σR) (cG cM cR : ℕ) (hG : 0 < cG) (hM : 0 < cM) (hR : 0 < cR) :
    (0 < gaussAlpha μ l₁ l₂ σM σR → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (((1 - ε) * (gaussAlpha μ l₁ l₂ σM σR)⁻¹ * √(2 * Real.log n) : ℝ) : EReal) ≤
        Vstar (gaussFramework μ l₁ l₂ σM σR cG cM cR hG hM hR) n ∧
      Vstar (gaussFramework μ l₁ l₂ σM σR cG cM cR hG hM hR) n ≤
        (((1 + ε) * (gaussAlpha μ l₁ l₂ σM σR)⁻¹ * √(2 * Real.log n) : ℝ) : EReal)) ∧
    (gaussAlpha μ l₁ l₂ σM σR = 0 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ((c * n : ℝ) : EReal) ≤ Vstar (gaussFramework μ l₁ l₂ σM σR cG cM cR hG hM hR) n ∧
      Vstar (gaussFramework μ l₁ l₂ σM σR cG cM cR hG hM hR) n ≤ ((C * n : ℝ) : EReal)) ∧
    (gaussAlpha μ l₁ l₂ σM σR < 0 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ((Real.exp (c * n) : ℝ) : EReal) ≤ Vstar (gaussFramework μ l₁ l₂ σM σR cG cM cR hG hM hR) n ∧
      Vstar (gaussFramework μ l₁ l₂ σM σR cG cM cR hG hM hR) n ≤
        ((Real.exp (C * n) : ℝ) : EReal)) := by sorry

end GMRDiversity.Supplement
