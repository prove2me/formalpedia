-- Prove2me | Theorems.Thm_GeoSemialgCSP_lemma_4_1
-- name    : GeoSemialgCSP.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:51.438195+00:00
-- url     : https://prove2.me/theorems/9918f042-2631-4f5e-a447-92123209b8ba
-- title:
--   Lemma 4.1 — soundness of the multiscale instance [Chatziafratis–Makarychev 2023]
-- statement:
--   This is the soundness of the multiscale instance, stated by Chatziafratis and Makarychev (2023, Lemma 5.1) and proved in Section 8 of their paper.
--
--   Let $k\ge2$. For every integer $q_0\ge1$ and every $\varepsilon>0$ there is $h_0$ such that every height $h\ge h_0$ has the following property: for every $q\le q_0$ and every payoff $f:[q]^k\to[0,1]$,
--   $$\mathrm{OPT}(\tilde I_f)\ \le\ \alpha^*_f+\varepsilon ,$$
--   where $\tilde I$ is the multiscale template on the $k^h$ leaves of the complete ordered $k$-ary tree of height $h$.
--
--   It is the source of soundness of the dictatorship test: coarse solutions with boundedly many labels cannot beat the best biased random assignment on the multiscale instance.
--
--   Differences from the source:
--   - encoding: leaves of T_m and of T_M numbered 0, …, m−1 and 0, …, M−1 with M = k^H → words Fin h → Fin k and Fin H → Fin k; reason: a leaf's number is the base-k value of its word
--   - encoding: [q] = {0, …, q−1} → Fin q; reason: index base
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.1, p.10 (PDF p.11), citing Chatziafratis–Makarychev 2023, Lemma 5.1

import Mathlib
import Definitions.Def_GeoSemialgCSP_MSSound

namespace GeoSemialgCSP

/-- **Lemma 4.1 (soundness of the multiscale instance).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.1, printed p.10 (PDF p.11),
citing Chatziafratis–Makarychev (2023, Lemma 5.1): for every integer `q₀ ≥ 1` and every `ε > 0`,
all sufficiently large heights `h` have the property that for every `q ≤ q₀` and every payoff
`f : [q]^k → [0,1]`, `OPT(Ĩ_f) ≤ α*_f + ε`.

**Formalization Note.** "All sufficiently large heights" is `∃ h₀, ∀ h ≥ h₀`. -/
theorem lemma_4_1 {k : ℕ} (hk : 2 ≤ k) (q₀ : ℕ) (hq₀ : 1 ≤ q₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → MSSound k q₀ ε h := by sorry

end GeoSemialgCSP
