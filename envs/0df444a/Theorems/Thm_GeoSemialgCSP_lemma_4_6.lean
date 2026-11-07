-- Prove2me | Theorems.Thm_GeoSemialgCSP_lemma_4_6
-- name    : GeoSemialgCSP.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:14.464541+00:00
-- url     : https://prove2.me/theorems/fd42f7c6-b49b-4895-a759-f59a901b5f01
-- title:
--   Lemma 4.6 — fractional coarse soundness
-- statement:
--   Let $k\ge2$, let $h\ge1$ be a height with the property of Lemma 4.1 for $q_0\ge1$ and $\varepsilon>0$, and let $L$ be a random map with items 1–3 of Lemma 4.2 for some error $\varepsilon_L>0$. For every $R$, every $q\le q_0$, every payoff $f:[q]^k\to[0,1]$ and every $F:[M]^R\to\mathcal P_q$,
--   $$\mathrm{val}(F,(J_R)_f)\ \le\ \alpha^*_f+\varepsilon .$$
--
--   The multiscale soundness of Lemma 4.1 survives the random embedding and fractional labels.
--
--   Differences from the source:
--   - encoding: leaves of T_m and of T_M numbered 0, …, m−1 and 0, …, M−1 with M = k^H → words Fin h → Fin k and Fin H → Fin k; reason: a leaf's number is the base-k value of its word
--   - generalization: R ≥ 1 (Let R ≥ 1, p.11) → every R : ℕ; reason: the R ≥ 1 cases are included; at R = 0 the test has a single variable and the inequality also holds
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.6, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_GeoSemialgCSP_MSSound
import Definitions.Def_GeoSemialgCSP_RE1
import Definitions.Def_GeoSemialgCSP_RE2
import Definitions.Def_GeoSemialgCSP_RE3
import Definitions.Def_GeoSemialgCSP_valJ
import Definitions.Def_GeoSemialgCSP_alphaF

namespace GeoSemialgCSP

/-- **Lemma 4.6 (fractional coarse soundness).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 4.6, printed p.13 (PDF p.14): for
every `q ≤ q₀`, every `f : [q]^k → [0,1]` and every `F : [M]^R → P_q`, `val(F, (J_R)_f) ≤ α*_f + ε`.

**Formalization Note.** `h ≥ 1` is any height satisfying Lemma 4.1 for `q₀, ε` (the section's
fixed height; `h ≥ 1` makes the template have total weight one, p.9) and `L` satisfies items 1–3 of Lemma 4.2. The predicate `P` does not occur. -/
theorem lemma_4_6 {k : ℕ} (hk : 2 ≤ k) (q₀ : ℕ) (ε : ℝ) (hq₀ : 1 ≤ q₀) (hε : 0 < ε) {h H : ℕ} (hh : 1 ≤ h) (hms : MSSound k q₀ ε h)
    (L : PMF ((Fin h → Fin k) → Wd k H)) (εL : ℝ) (hεL : 0 < εL)
    (hL1 : RE1 L) (hL2 : RE2 L) (hL3 : RE3 L εL)
    (R q : ℕ) (hq : q ≤ q₀) (f : (Fin k → Fin q) → ℝ) (hf : ∀ a, f a ∈ Set.Icc (0 : ℝ) 1)
    (F : (Fin R → Wd k H) → Fin q → ℝ) (hF : ∀ z, F z ∈ stdSimplex ℝ (Fin q)) :
    valJ L R f F ≤ alphaF f + ε := by sorry

end GeoSemialgCSP
