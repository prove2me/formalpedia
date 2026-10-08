-- Prove2me | Theorems.Thm_GenEmpLik_Consistency_display_after_47
-- name    : GenEmpLik.Consistency.display_after_47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:53:34.796607+00:00
-- url     : https://prove2.me/theorems/c3a02def-27aa-4e5b-af70-ddb860b8e12a
-- title:
--   Display after (47) — E_{P̂n}[|L − 1|^p]^{1/p} ≤ n^{−1/p} √(ρ C_f)
-- statement:
--   Let $n\ge1$, $r\ge2$ (the exponent $\max\{2,1+1/\epsilon\}$ of (47)), $\rho\in\mathbb R$, and let $C_f$ be a constant as in Lemma 13: $\|nw-\mathbb 1\|_2\le\sqrt{\rho C_f}$ for every $w$ in the ball $\{w\ge0:\sum_i w_i=1,\ \sum_i f(nw_i)\le\rho\}$. Then for every $w$ in that ball, with likelihood ratio $L(\xi_i)=nw_i$,
--
--   $$
--   E_{\widehat P_n}\big[|L(\xi)-1|^r\big]^{1/r}
--   =n^{-1/r}\,\|nw-\mathbb 1\|_r
--   \ \le\ n^{-1/r}\,\|nw-\mathbb 1\|_2
--   \ \le\ n^{-1/r}\sqrt{\rho C_f},
--   $$
--
--   where $E_{\widehat P_n}[|L-1|^r]=\frac1n\sum_i|nw_i-1|^r$. Since $r<\infty$, the right side tends to $0$ as $n\to\infty$, which makes the reweighting term of (47) vanish.
--
--   **Formalization Note** The page writes $\sqrt{\rho/\gamma_f}$ with $\gamma_f$ undefined ("where $\gamma_f$ is as in the lemma"); Lemma 13's bound is $\sqrt{\rho C_f}$, so $\gamma_f=1/C_f$. Lemma 13 enters as the hypothesis on $C_f$; the paper's exponent $p$ is called $r$.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 46, App. E.1, proof of Theorem 7, display after (47)

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet

namespace GenEmpLik.Consistency

/-- The display after (47) (arXiv:1610.03425v3, App. E.1, proof of Theorem 7, p. 46). Let
`n ≥ 1`, `r ≥ 2` (the paper's `p = max{2, 1 + 1/ε}`), and let `C_f` be a constant as in
Lemma 13: `‖n w − 𝟙‖₂ ≤ √(ρ C_f)` for every `w` in the ball `{w ≥ 0 : ∑ wᵢ = 1,
∑ᵢ f(n wᵢ) ≤ ρ}`. Then for every `w` in the ball, with `L(ξᵢ) = n wᵢ`,
`E_{P̂n}[|L − 1|^r]^{1/r} = n^{−1/r} ‖n w − 𝟙‖_r ≤ n^{−1/r} ‖n w − 𝟙‖₂ ≤ n^{−1/r} √(ρ C_f)`.
(The page writes `√(ρ/γ_f)` with `γ_f` undefined; it is `√(ρ C_f)`.) -/
theorem display_after_47 (f : ℝ → EReal) (ρ : ℝ) (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 2 ≤ r)
    (Cf : ℝ)
    (hCf : ∀ w ∈ PhiDivRobust.Counterpart.probUncertaintySet f
        (fun _ : Fin n => (1 : ℝ) / n) (ρ / n),
      Real.sqrt (∑ i, ((n : ℝ) * w i - 1) ^ 2) ≤ Real.sqrt (ρ * Cf))
    (w : Fin n → ℝ) (hw : w ∈ PhiDivRobust.Counterpart.probUncertaintySet f
      (fun _ : Fin n => (1 : ℝ) / n) (ρ / n)) :
    ((1 / (n : ℝ)) * ∑ i, |(n : ℝ) * w i - 1| ^ r) ^ (1 / r) =
        (n : ℝ) ^ (-(1 / r)) * (∑ i, |(n : ℝ) * w i - 1| ^ r) ^ (1 / r) ∧
      (n : ℝ) ^ (-(1 / r)) * (∑ i, |(n : ℝ) * w i - 1| ^ r) ^ (1 / r) ≤
        (n : ℝ) ^ (-(1 / r)) * Real.sqrt (∑ i, ((n : ℝ) * w i - 1) ^ 2) ∧
      (n : ℝ) ^ (-(1 / r)) * Real.sqrt (∑ i, ((n : ℝ) * w i - 1) ^ 2) ≤
        (n : ℝ) ^ (-(1 / r)) * Real.sqrt (ρ * Cf) := by sorry

end GenEmpLik.Consistency
