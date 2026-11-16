-- Prove2me | Theorems.Thm_HMajConsensus_Supplement_theorem_8_4_lower_bound
-- name    : HMajConsensus.Supplement.theorem_8_4_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:44:54.877954+00:00
-- url     : https://prove2.me/theorems/928ea611-8fa0-4a82-a026-6e48fd7c7b67
-- title:
--   Theorem 8.4 — every neutral $h$-input dynamics needs $\Omega(1+\min\{1/\min\{h^2p_{\max}(0),1\},\sqrt n/(h\sqrt{\log n})\})$ rounds w.p. $\ge1-1/n$, with the $P_{\mathrm{ignore}}$ refinement
-- statement:
--   Let $n\ge2$ vertices hold opinions in $[k]$, $k\ge2$, and let $h\ge1$. Let $\mathcal L_{\mathcal W}$ be a **neutral $h$-input rule** and consider its $\mathcal W$-dynamics started from a configuration $C(0)$ whose maximum opinion density satisfies $p_{\max}(0)<1$. Write $\tau_{\mathrm{consensus}}$ for the first round at which all vertices agree. There is an absolute constant $c>0$, independent of $n,k,h$, the rule, $P_{\mathrm{ignore}}$ and $C(0)$, such that:
--
--   1. With probability at least $1-1/n$, $\tau_{\mathrm{consensus}}\ge T$, where
--   $$T=c\left(1+\min\left\{\frac{1}{\min\{h^2p_{\max}(0),1\}},\ \frac{\sqrt n}{h\sqrt{\log n}}\right\}\right).$$
--   2. If moreover the rule is $P_{\mathrm{ignore}}$-ignoring for some $P_{\mathrm{ignore}}\in[0,1]$, then with probability at least $1-1/n$, $\tau_{\mathrm{consensus}}\ge T$ with
--   $$T=c\left(1+\min\left\{\frac{1}{\min\{h^2p_{\max}(0),1\}},\ \frac{n}{h^2\log n},\ \frac{\sqrt n}{h\sqrt{(1-P_{\mathrm{ignore}})\log n}}\right\}\right),$$
--   where the last term is omitted when $P_{\mathrm{ignore}}=1$.
--   3. In particular, for a $1$-ignoring rule, with probability at least $1-1/n$, $\tau_{\mathrm{consensus}}\ge T$ with
--   $$T=c\left(1+\min\left\{\frac{1}{\min\{h^2p_{\max}(0),1\}},\ \frac{n}{h^2\log n}\right\}\right).\tag{52}$$
--
--   This is the paper's lower bound (stated informally as Theorem 1.3). Together with the upper bound of Theorem 1.1 it shows that $h$-Majority is optimal up to polylogarithmic factors among neutral $h$-input dynamics, and it gives the consensus-time lower bounds for 2-Choices and DéjàVu.
--
--   **Formalization Note** $\log$ is the natural logarithm (`Real.log`). "The consensus time is at least $T$" is the event that no round $t$ with $t<T$ is a consensus configuration. The omitted term for $P_{\mathrm{ignore}}=1$ is an explicit case split, because in Lean $x/0=0$ would otherwise make the minimum $0$.
--
--   Differences from the source:
--   - encoding: $T=\Omega(\cdot)$, possibly with a different hidden constant in each of the three claims → one absolute constant $c>0$ quantified before $n,k,h$, the rule, $P_{\mathrm{ignore}}$ and $C(0)$, with $T=c\,(\cdot)$; reason: Ω asserts such a constant, and the minimum of three constants serves all three claims, so the statements are equivalent.
--   - encoding: "the consensus time is at least $T$" → no round $t\in\mathbb N$ with $(t:\mathbb R)<T$ is a consensus configuration; reason: this is $\tau_{\mathrm{consensus}}\ge T$ without an infimum that would send never-ending paths to $0$.
--   - encoding: "the last term is omitted when $P_{\mathrm{ignore}}=1$" → `if Pignore = 1 then min of two terms else min of three terms`; reason: the literal term would be $\sqrt n/(h\cdot0)=0$ in Lean.
--   - encoding: opinions $[k]$, vertices $[n]$, the law $\mathcal L_{\mathcal W}$ → `Fin k`, `Fin n`, a `PMF` on functions `Fin k → (Fin h → Fin k) → Fin k`, the dynamics as the Markov-chain path law of the per-round product kernel; reason: Lean conventions, same instances.
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Theorem 8.4 (Eq. (52)), p.54 (PDF p.56); informal restatement Theorem 1.3, p.3

import Mathlib
import Definitions.Def_HMajConsensus_pathLaw
import Definitions.Def_HMajConsensus_Supplement_wPathLaw

open MeasureTheory ProbabilityTheory

namespace HMajConsensus.Supplement

/-- **Theorem 8.4** (= Theorem 1.3; d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal
Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §8.1, p.54): suppose
`pmax(0) < 1` and `h ≥ 1`. For any neutral `h`-input dynamics the consensus time is at least
`T` with probability at least `1 − 1/n`, where
`T = Ω(1 + min{1/min{h²pmax(0), 1}, √n/(h√log n)})`. If the dynamics is `P_ignore`-ignoring,
`T = Ω(1 + min{1/min{h²pmax(0), 1}, n/(h² log n), √n/(h√((1 − P_ignore) log n))})`, the last
term omitted when `P_ignore = 1`; in particular, for `P_ignore = 1`,
`T = Ω(1 + min{1/min{h²pmax(0), 1}, n/(h² log n)})` (Eq. (52)).

**Formalization Note** `Ω` is one absolute constant `c > 0` chosen before `n, k, h`, the rule
`L_W`, `P_ignore` and `C(0)`; `T = c·(1 + min{…})`. `n ≥ 2` and `k ≥ 2` are the standing
assumptions of Definitions 8.1 and 8.3. "The consensus time is at least `T`" is
`ConsensusNotBefore T`. `log` is `Real.log`. The case `P_ignore = 1` is an explicit `if`, since
in Lean `x / 0 = 0` would otherwise make the minimum `0`. -/
theorem theorem_8_4_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n k h : ℕ), 2 ≤ n → 2 ≤ k → 1 ≤ h →
      ∀ (L : PMF (RuleFun k h)), IsHInputRule L → IsNeutral L →
      ∀ C₀ : Config n k, pmax C₀ < 1 →
        (1 - 1 / (n : ℝ) ≤ (wPathLaw L C₀ {ω | ConsensusNotBefore
            (c * (1 + min (1 / min ((h : ℝ) ^ 2 * pmax C₀) 1)
              (Real.sqrt n / (h * Real.sqrt (Real.log n))))) ω}).toReal) ∧
        (∀ Pignore : ℝ, 0 ≤ Pignore → Pignore ≤ 1 → IsIgnoring L Pignore →
          1 - 1 / (n : ℝ) ≤ (wPathLaw L C₀ {ω | ConsensusNotBefore
            (c * (1 + if Pignore = 1 then
                min (1 / min ((h : ℝ) ^ 2 * pmax C₀) 1) (n / ((h : ℝ) ^ 2 * Real.log n))
              else
                min (min (1 / min ((h : ℝ) ^ 2 * pmax C₀) 1) (n / ((h : ℝ) ^ 2 * Real.log n)))
                  (Real.sqrt n / (h * Real.sqrt ((1 - Pignore) * Real.log n))))) ω}).toReal) ∧
        (IsIgnoring L 1 →
          1 - 1 / (n : ℝ) ≤ (wPathLaw L C₀ {ω | ConsensusNotBefore
            (c * (1 + min (1 / min ((h : ℝ) ^ 2 * pmax C₀) 1)
              (n / ((h : ℝ) ^ 2 * Real.log n)))) ω}).toReal) := by sorry

end HMajConsensus.Supplement
