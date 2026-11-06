-- Prove2me | Theorems.Thm_FullPathSCC_ln_monotone_certainty_equivalent
-- name    : FullPathSCC.ln_monotone_certainty_equivalent
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:21:36.618487+00:00
-- url     : https://prove2.me/theorems/a5579196-d36f-4894-97c0-d56659dd9f20
-- title:
--   Proof of Theorem A.2, p.7601 — "ln is a monotonically increasing function": the one-step certainty equivalent is monotone
-- statement:
--   Let $\mathcal S$ be a finite set, $\kappa>0$, $\beta\ge0$, and let $q$ be a probability vector on $\mathcal S$ ($q_j\ge0$, $\sum_jq_j=1$). If $v,w:\mathcal S\to\mathbb R$ satisfy $v_j\le w_j$ for every $j$, then
--
--   $$
--   -\frac1\kappa\ln\sum_{j\in\mathcal S}q_j e^{-\kappa\beta v_j}\ \le\ -\frac1\kappa\ln\sum_{j\in\mathcal S}q_j e^{-\kappa\beta w_j}.
--   $$
--
--   With $\kappa=k_t$ and $q=p_{\vartheta_t,\cdot}(T_t)$ this is the monotonicity of the certainty equivalent in (7)–(8) in the continuation values, which the proof of Theorem A.2 obtains from the monotonicity of $\ln$ and uses to compare every plan with $V^*$.
--
--   Differences from the source:
--   - generalization: "the fact that ln is a monotonically increasing function", used for the certainty equivalent of (7) with $\kappa=k_t$, $q=p_{\vartheta_t,\cdot}(T_t)$, $0<\beta<1$, $\mathcal S=\{1,2,3,4\}$ → monotonicity of $-\frac1\kappa\ln\sum_jq_je^{-\kappa\beta v_j}$ in $v$ for every $\kappa>0$, $\beta\ge0$ and probability vector $q$ on a finite set; reason: the page states the monotonicity of ln and uses this consequence; the case of (8) is an instance
-- source:
--   Zhao, Basu, Lontzek & Schmedders, The Social Cost of Carbon When We Wish for Full-Path Robustness, Management Science 69(12) (2023), doi:10.1287/mnsc.2023.4736, proof of Theorem A.2, p.7601, "the fact that ln is a monotonically increasing function"

import Mathlib

namespace FullPathSCC

/-- **"the fact that ln is a monotonically increasing function"**, proof of Theorem A.2
(Management Science 69(12) (2023), p.7601): the one-step certainty equivalent of (7)–(8) is
monotone in the continuation values. For `κ > 0`, `β ≥ 0`, a probability vector `q` on a finite
set `𝒮` and `v ≤ w` pointwise,
`−(1/κ) ln Σ_j q_j e^{−κβ v_j} ≤ −(1/κ) ln Σ_j q_j e^{−κβ w_j}`.

**Formalization Note** In (8), `κ = k_t` and `q = p_{ϑ_t,·}(T_t)`. -/
theorem ln_monotone_certainty_equivalent {S : Type*} [Fintype S] (κ β : ℝ) (hκ : 0 < κ)
    (hβ : 0 ≤ β) (q : S → ℝ) (hq : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) (v w : S → ℝ)
    (hvw : ∀ j, v j ≤ w j) :
    -(1 / κ) * Real.log (∑ j, q j * Real.exp (-κ * β * v j)) ≤
      -(1 / κ) * Real.log (∑ j, q j * Real.exp (-κ * β * w j)) := by sorry

end FullPathSCC
