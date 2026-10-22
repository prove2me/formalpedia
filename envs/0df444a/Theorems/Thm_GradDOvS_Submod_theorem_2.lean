-- Prove2me | Theorems.Thm_GradDOvS_Submod_theorem_2
-- name    : GradDOvS.Submod.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:18:09.087378+00:00
-- url     : https://prove2.me/theorems/ec847c84-04d1-42b4-8fd5-99cecc7c28f2
-- title:
--   Theorem 2, p. 20 (PGS part; constants of EC.2.2, corrected truncation level) — truncated projected SSGD on the Lovász extension with rounding returns an (ε, δ)-PGS solution
-- statement:
--   Let $d \ge 1$, let $f : \{0,1\}^d \to \mathbb R$ be submodular with $|f(A) - f(B)| \le L$ for all $A,B$, and let the simulation oracle satisfy Assumption 1 with $\sigma > 0$. Let $\epsilon > 0$, $0<\delta<1$, and choose $T, M, n$ with
--   $$T \ge \frac{3584\, d\sigma^2}{\epsilon^2}\log\frac2\delta, \qquad T \ge \frac{2\epsilon}{\sigma}, \qquad T \ge 4,$$
--   $$M \ge L + 2\sigma\sqrt{\log\frac{4\sigma d T}{\epsilon}}, \qquad 64 d^2 M^2 \le \epsilon^2 T, \qquad n \ge \frac{32\sigma^2}{\epsilon^2}\log\frac{8d}{\delta}.$$
--   Run Algorithm 2 from any $x^0 = \mathbb 1_{A_0}$ with the estimator (4), truncation level $M$ and step size $\eta = 1/(M\sqrt T)$, and round the average $\bar x = \frac1T\sum_{t<T} x^t$ by Algorithm 1 with $n$ replications per neighbouring point. Then the returned set $S$ satisfies
--   $$\mathbb P\Big(f(S) > \min_{A} f(A) + \epsilon\Big) \le \delta,$$
--   whatever minimizer of the sample means is returned: the algorithm returns an $(\epsilon,\delta)$-PGS solution of stochastic submodular minimization.
--
--   The exact simulation count is $2dT + (d+1)n$ evaluations. The Lean hypotheses give lower bounds on $T$ and $n$, so this statement does not assert an upper bound on that count.
--
--   **Formalization Note** The printed theorem fixes the parameters only up to $\tilde\Theta$; the constants are those of its proof (p. ec7, PDF 45), where "$\delta$ is small enough" means exactly $64d^2M^2 \le \epsilon^2T$ and $T \ge \max\{2\epsilon/\sigma, 4\}$, both stated as hypotheses. The truncation level is **corrected** from the printed $M = \max\{L, 2\sigma\sqrt{\log(4\sigma dT/\epsilon)}\}$ (Lemma EC.3) to $M \ge L + 2\sigma\sqrt{\log(4\sigma dT/\epsilon)}$, because Lemma EC.2, on which the proof rests, fails at the printed level (counterexample in the note to Lemma EC.2). The rounding uses the fixed sample size of Theorem 1's proof with $\sigma^2$ restored. The cost bound $T(\epsilon,\delta,\mathcal{MC})$ is not formalized. Assumption 3 ($X = [N]^d$) is not used: §3's decision space is $\{0,1\}^d$.
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 20, Theorem 2; constants from the proof, p. ec7 (PDF 45), and Lemmas EC.2–EC.3, pp. ec3–ec4 (PDF 41–42) (corrected; see Formalization Note)

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace GradDOvS.Submod

/-- Theorem 2, p. 20 (PGS part), with the constants of its proof (EC.2.2, p. ec7 = PDF 45) and the
corrected truncation level `M ≥ L + 2σ√log(4σdT/ε)`: Algorithm 2 with `η = 1/(M√T)`, followed by the
rounding of Algorithm 1 with `n` replications per neighbouring point, returns an `(ε, δ)`-PGS
solution of stochastic submodular minimization on `{0,1}^d`. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] {d T n : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Finset (Fin d) → ℝ) (L : ℝ) (σ : NNReal)
    (Z : Slot d T n → Ω → Finset (Fin d) → ℝ) (hZ : IsSimOracle P f σ Z)
    (hf : Standing L f) (hσ : 0 < σ) (ε δ M : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hT₁ : 3584 * d * (σ : ℝ) ^ 2 / ε ^ 2 * Real.log (2 / δ) ≤ T)
    (hT₂ : 2 * ε / (σ : ℝ) ≤ T) (hT₃ : 4 ≤ T)
    (hM : L + 2 * (σ : ℝ) * Real.sqrt (Real.log (4 * σ * d * T / ε)) ≤ M)
    (hMT : 64 * (d : ℝ) ^ 2 * M ^ 2 ≤ ε ^ 2 * T)
    (hn : 32 * (σ : ℝ) ^ 2 / ε ^ 2 * Real.log (8 * d / δ) ≤ n)
    (A₀ : Finset (Fin d)) :
    P (roundFail f ε Z (ssgdAvg Z (1 / (M * Real.sqrt T)) M A₀)) ≤ ENNReal.ofReal δ := by sorry

end GradDOvS.Submod
