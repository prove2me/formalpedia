-- Prove2me | Theorems.Thm_KWPurify_Rate_lemma_6_1
-- name    : KWPurify.Rate.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:55.952153+00:00
-- url     : https://prove2.me/theorems/36ee7ed6-bf75-427b-9d3d-37ba72829c5b
-- title:
--   Lemma 6.1 (corrected domain $[0,1]$) — $\sum_s w_N(s) f_N(2s/N) \to f_\infty(\lambda)$
-- statement:
--   Let $\beta > 0$ and $\lambda = \tanh\beta$. Let $f_N : \mathbb R \to \mathbb R$, $N \in \mathbb N$, be functions such that
--
--   1. they are uniformly bounded on $[0,1]$: $|f_N(x)| \le C$ for all $N$ and all $x \in [0,1]$;
--   2. each $f_N$ is continuous on $(0,1)$;
--   3. for some $\delta > 0$, $f_N \to f_\infty$ uniformly on $(\lambda-\delta,\lambda+\delta)$, where $f_\infty$ is continuous on that interval.
--
--   Then, with the weights $w_N(s)$ of eq. (14),
--   $$\lim_{N\to\infty}\ \sum_{s\in I[N]} w_N(s)\, f_N\!\Big(\frac{2s}{N}\Big) = f_\infty(\lambda).$$
--
--   In other words the probability distributions $\sum_s w_N(s)\,\delta_{2s/N}$ on $[0,1]$ converge to the point mass at $\lambda$. This is the step that turns the finite-$N$ formula of Theorem 5.1 into a limit.
--
--   **Formalization Note** Corrected statement: the paper takes $f_N : (0,1) \to \mathbb R$, but the sum evaluates $f_N$ at $2s/N = 1$ for every $N$ (and at $0$ for even $N$), so boundedness is required on the closed interval $[0,1]$. Spins are encoded by $k = N/2 - s$, so $2s/N = (N-2k)/N$; at $N = 0$ the quotient is $0/0 = 0$ in Lean, which does not affect the limit.
-- source:
--   Keyl & Werner, The Rate of Optimal Purification procedures, arXiv:quant-ph/9910124v1, pp. 18–19, Lemma 6.1, eq. (38) (domain corrected to [0, 1])

import Mathlib
import Definitions.Def_KWPurify_Rate_Blocks

open Filter Topology

namespace KWPurify.Rate
theorem lemma_6_1 (β : ℝ) (hβ : 0 < β) (f : ℕ → ℝ → ℝ) (finf : ℝ → ℝ)
    (hbdd : ∃ C : ℝ, ∀ N : ℕ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |f N x| ≤ C)
    (hcont : ∀ N : ℕ, ContinuousOn (f N) (Set.Ioo 0 1))
    (δ : ℝ) (hδ : 0 < δ)
    (hcontinf : ContinuousOn finf (Set.Ioo (Real.tanh β - δ) (Real.tanh β + δ)))
    (hunif : TendstoUniformlyOn f finf atTop
      (Set.Ioo (Real.tanh β - δ) (Real.tanh β + δ))) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N / 2 + 1),
        spinWeight β N k * f N (((N - 2 * k : ℕ) : ℝ) / (N : ℝ)))
      atTop (𝓝 (finf (Real.tanh β))) := by sorry
end KWPurify.Rate
