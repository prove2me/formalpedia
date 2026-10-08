-- Prove2me | Theorems.Thm_KalaiVempala_Lazy_lemma_1_2
-- name    : KalaiVempala.Lazy.lemma_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:22.698975+00:00
-- url     : https://prove2.me/theorems/96b885ed-c967-4b9a-b02a-39024308a52b
-- title:
--   Lemma 1.2, p. 295 — FLL(ε), FLL*(ε) match FPL(ε), FPL*(ε) in expectation each period and update with probability at most εA
-- statement:
--   **Follow the Lazy Leader.** Let $\mathcal D \subset \mathbb R^n$ be a decision set with $|d - d'|_1 \le D$ for all $d, d' \in \mathcal D$, let $M$ be a measurable argmin oracle for $\mathcal D$ ($M(x) \in \mathcal D$ minimises $d \cdot x$), let $\mathcal S \subset \mathbb R^n$ be a state set with $|x|_1 \le A$ for all $x \in \mathcal S$, and let $s_1, s_2, \dots \in \mathcal S$ be a fixed state sequence with $s_{1:t} = s_1 + \dots + s_t$. Let $\varepsilon > 0$, let $U$ be the uniform law on $[0, 1/\varepsilon]^n$ and $\mu$ the law with density $(\varepsilon/2)^n e^{-\varepsilon|x|_1}$.
--
--   The algorithms:
--   - FPL($\varepsilon$) plays $M(s_{1:t-1} + p)$ with $p \sim U$; FPL\*($\varepsilon$) plays $M(s_{1:t-1} + p)$ with $p \sim \mu$.
--   - FLL($\varepsilon$) draws $p \sim U$ once and plays $M(g_{t-1})$, where $g_{t-1} = g(s_{1:t-1}, p)$ is the unique point of the grid $p + \tfrac1\varepsilon\mathbb Z^n$ in $s_{1:t-1} + [0, 1/\varepsilon)^n$.
--   - FLL\*($\varepsilon$) draws $p_1 \sim \mu$, plays $M(s_{1:t-1} + p_t)$, and updates $p_{t+1} = p_t - s_t$ with probability $\min\{1, d\mu(p_t - s_t)/d\mu(p_t)\}$, otherwise $p_{t+1} = -p_t$. Write $\nu_t$ for the law of $p_t$.
--
--   Then for every period $t \ge 1$:
--
--   1. FLL and FPL have identical expectations: $\mathbb E_{p\sim U}\big[s_t \cdot M(g(s_{1:t-1}, p))\big] = \mathbb E_{p \sim U}\big[s_t \cdot M(s_{1:t-1} + p)\big]$;
--   2. FLL performs an update with probability at most $\varepsilon A$: $\Pr_{p \sim U}[g_{t-1} \ne g_t] \le \varepsilon A$;
--   3. FLL\* and FPL\* have identical expectations: $\mathbb E_{p_t \sim \nu_t}\big[s_t \cdot M(s_{1:t-1} + p_t)\big] = \mathbb E_{p \sim \mu}\big[s_t \cdot M(s_{1:t-1} + p)\big]$;
--   4. FLL\* performs an update with probability at most $\varepsilon A$:
--   $$\Pr\big[\, s_{1:t} + p_{t+1} \ne s_{1:t-1} + p_t \,\big] \le \varepsilon A .$$
--
--   The lazy algorithms thus have the same per-period expected cost as FPL and FPL\*, hence the guarantees of Theorem 1.1 of the paper, against an oblivious adversary, while calling the offline oracle only with probability at most $\varepsilon A$ per period.
--
--   **Formalization Note** "Performing an update" on period $t$ is the event that the point at which the oracle is evaluated changes once $s_t$ is seen: $g_{t-1} \ne g_t$ for FLL, and $s_{1:t} + p_{t+1} \ne s_{1:t-1} + p_t$ for FLL\*, measured under the joint law `fllStarJoint ε (s t) ν_t` of $(p_t, p_{t+1})$. "Identical expectations" compares the expected cost on period $t$ for the same $M$ and the same states. The adversary is oblivious: $s$ is a fixed sequence, as in the lemma's "for any fixed sequence of states". Added hypotheses, not on the page: measurability of $M$ (the expectations need it) and $\varepsilon > 0$ (the algorithms divide by $\varepsilon$). The argmin property and the diameter bound $D$ are the paper's standing setting; they make every integrand bounded and hence integrable, so claims 1 and 3 compare genuine expectations. The proofs of the four claims do not use the argmin property. States are indexed from $1$ (`s 0` is unused).
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 295, Lemma 1.2 (proofs: §3.1, pp. 302–303, FLL case; §4, p. 304, FLL* case)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Lazy_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Lazy

theorem lemma_1_2 {n : ℕ} (Dset S : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : KalaiVempala.Additive.IsArgminOracle Dset M) (hMmeas : Measurable M)
    (Ddiam : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (A : ℝ) (hA : ∀ x ∈ S, ∑ i, |x i| ≤ A)
    (s : ℕ → Fin n → ℝ) (hs : ∀ t, 1 ≤ t → s t ∈ S) (ε : ℝ) (hε : 0 < ε) :
    ∀ t, 1 ≤ t →
      (∫ p, s t ⬝ᵥ M (fllGridPoint ε (prefixSum s (t - 1)) p) ∂(perturbLaw n ε) =
          ∫ p, s t ⬝ᵥ M (prefixSum s (t - 1) + p) ∂(perturbLaw n ε)) ∧
      perturbLaw n ε {p | fllGridPoint ε (prefixSum s (t - 1)) p ≠
          fllGridPoint ε (prefixSum s t) p} ≤ ENNReal.ofReal (ε * A) ∧
      (∫ p, s t ⬝ᵥ M (prefixSum s (t - 1) + p) ∂(fllStarLaw ε s t) =
          ∫ p, s t ⬝ᵥ M (prefixSum s (t - 1) + p) ∂(KalaiVempala.Multiplicative.laplaceLaw n ε)) ∧
      fllStarJoint ε (s t) (fllStarLaw ε s t)
          {q | prefixSum s t + q.2 ≠ prefixSum s (t - 1) + q.1} ≤ ENNReal.ofReal (ε * A) := by sorry

end KalaiVempala.Lazy
