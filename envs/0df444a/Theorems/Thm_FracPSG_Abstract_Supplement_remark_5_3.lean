-- Prove2me | Theorems.Thm_FracPSG_Abstract_Supplement_remark_5_3
-- name    : FracPSG.Abstract.Supplement.remark_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:58:52.62899+00:00
-- url     : https://prove2.me/theorems/acd135de-2175-416c-ac5b-af6a014b8bee
-- title:
--   Remark 5.3 — inf βₙ > 0 and εₙ = O(h(z_{n−ı̄}) − h(z_{n+1−ı̲})) give the parameter conditions of Lemma 5.1(iii) and Theorem 5.2(iv)
-- statement:
--   Work in the abstract framework of §5: $h:\mathcal K\to(-\infty,+\infty]$ proper and lower semicontinuous on a finite-dimensional real Hilbert space $\mathcal K$, a sequence $(z_n)$ in $\mathcal K$, positive sequences $(\alpha_n)$, $(\beta_n)$, nonnegative sequences $(\varepsilon_n)$, $(\Delta_n)$ with $\Delta_k=0$ for $k<0$, integers $\underline\imath\le\bar\imath$, and weights $\lambda_i\ge0$ on $I=\{\underline\imath,\dots,\bar\imath\}$ summing to $1$. Assume the sufficient decrease condition (H1), $h(z_{n+1})+\alpha_n\Delta_n^2\le h(z_n)$, and the parameter condition (H4), $\inf\alpha_n>0$, $\inf\alpha_n\beta_n>0$, $\sum\varepsilon_n<\infty$. If $\inf_n\beta_n>0$, then:
--
--   1. the conditions of Lemma 5.1(iii) hold:
--   $$\inf_{n\in\mathbb N,\,i\in I}\alpha_{n-i}\beta_n^2>0\qquad\text{and}\qquad \lim_{n\to\infty}\frac{\varepsilon_n}{\beta_n}=0;$$
--   2. if moreover $\varepsilon_n=O\big(h(z_{n-\bar\imath})-h(z_{n+1-\underline\imath})\big)$ as $n\to\infty$, then the parameter conditions of Theorem 5.2(iv) hold:
--   $$\frac{\varepsilon_n}{\beta_n}=O\Big(\sqrt{h(z_{n-\bar\imath})-h(z_{n+1-\underline\imath})}\Big)\quad\text{and}\quad \sum_{k=n}^{\infty}\varepsilon_k=O\Big(\sqrt{h(z_{n-\bar\imath})-h(\bar z)}\Big),$$
--   the second for every $\bar z\in\Omega_0=\{\bar z\text{ a cluster point of }(z_n): h(z_n)\to h(\bar z)\}$.
--
--   The remark is how the abstract theorem is applied: in Theorem 5.5 the error term $\varepsilon_n$ is a multiple of a decrease of $h$, and this remark turns that into the hypotheses of Theorem 5.2.
--
--   **Formalization Note** The setting, (H1), (H4), $\Omega_0$ and the positivity of $\inf\alpha_{n-i}\beta_n^2$ are the published definitions of `FracPSG.Abstract.Basic`. Each $O(\cdot)$ is "there is $C$ such that eventually $\cdot\le C\cdot$". Values of $h$ enter as real numbers (`EReal.toReal`), as in the published Theorem 5.2; indices $n-\bar\imath$ and $n+1-\underline\imath$ are truncated at $0$, which affects only finitely many $n$. The tail sum is `∑' k, ε (n + k)`, finite by (H4).
--
--   Differences from the source:
--   - reading: the setting of the remark: the framework of §5 under the hypotheses of Theorem 5.2, with h(zₙ) ↓ h(z̄) → the §5 setting with (H1) and (H4) only; the second O-condition for every z̄ ∈ Ω₀; reason: the remark cites (H4) and h(zₙ) ↓ h(z̄); (H1) gives the monotonicity and z̄ ∈ Ω₀ the limit, so (H2), (H3), boundedness and KL are not needed
--   - generalization: hypotheses (H1)–(H4) of Theorem 5.2 → only (H1) and (H4); reason: dropping (H2) and (H3) gives a statement that specializes to the remark under the full hypotheses
--   - encoding: inf_{n∈ℕ,i∈I} α_{n−i}β_n² > 0 → DeltaLowerBound α β ı̲ ı̄ d for some d > 0 (a positive lower bound over the pairs with n − i ≥ 0); reason: the published encoding of the base mission; α_{n−i} is undefined for n − i < 0
--   - encoding: O(·) as n → +∞ and indices n − ı̄, n + 1 − ı̲ → ∃ C, ∀ᶠ n, … ≤ C · …, with indices through Int.toNat; reason: the encodings of the published FracPSG.Abstract.theorem_5_2; Int.toNat only changes finitely many n
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, pp. 17–18, Remark 5.3 (with its justification on p. 18)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracPSG_Abstract_Basic

open Filter Topology

namespace FracPSG.Abstract.Supplement

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL FracPSG.Abstract

/-- Remark 5.3 (Parameter conditions; Boţ–Dao–Li, arXiv:2003.04124v2, pp. 17–18). In the setting
of §5 with (H1) and (H4), if `inf βₙ > 0` then:
(1) `inf_{n, i ∈ I} α_{n−i} βₙ² > 0` and `εₙ/βₙ → 0` (the conditions of Lemma 5.1(iii));
(2) if moreover `εₙ = O(h(z_{n−ı̄}) − h(z_{n+1−ı̲}))`, then for every `z̄ ∈ Ω₀` (so `h(zₙ) ↓ h(z̄)`)
`εₙ/βₙ = O(√(h(z_{n−ı̄}) − h(z_{n+1−ı̲})))` and `∑_{k ≥ n} ε_k = O(√(h(z_{n−ı̄}) − h(z̄)))`, the
parameter conditions of Theorem 5.2(iv). Indices `n − ı̄`, `n + 1 − ı̲` are read through
`Int.toNat`, which only matters for finitely many `n`. -/
theorem remark_5_3 {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ}
    {lam : ℤ → ℝ}
    (hset : AbstractSetting h α β ε Δ ilo ihi lam)
    (hH1 : H1 h z α Δ) (hH4 : H4 α β ε)
    (hβ : ∃ b : ℝ, 0 < b ∧ ∀ n, b ≤ β n) :
    (∃ d : ℝ, DeltaLowerBound α β ilo ihi d) ∧
    Tendsto (fun n => ε n / β n) atTop (𝓝 0) ∧
    ((∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
        ε n ≤ C * ((h (z ((n : ℤ) - ihi).toNat)).toReal -
          (h (z ((n : ℤ) + 1 - ilo).toNat)).toReal)) →
      (∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
        ε n / β n ≤ C * Real.sqrt ((h (z ((n : ℤ) - ihi).toNat)).toReal -
          (h (z ((n : ℤ) + 1 - ilo).toNat)).toReal)) ∧
      ∀ zbar ∈ omega0 h z, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
        ∑' k : ℕ, ε (n + k) ≤
          C * Real.sqrt ((h (z ((n : ℤ) - ihi).toNat)).toReal - (h zbar).toReal)) := by sorry

end FracPSG.Abstract.Supplement
