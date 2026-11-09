-- Prove2me | Theorems.Thm_LinfContractionFP_eq_16
-- name    : LinfContractionFP.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:18.956852+00:00
-- url     : https://prove2.me/theorems/c30b8c48-57f2-4624-bea2-146ad982734b
-- title:
--   Eq. (16) — solving the recurrence of Theorem 1
-- statement:
--   For every $C_0>0$ there is $C$ such that the following holds for every $0<\gamma\le1$. Let $T:\mathbb N\times\mathbb R\to\mathbb R$ satisfy, for all $\varepsilon\in(0,1/4]$,
--   $$T_d(\varepsilon)\le C_0\,d^2\log_2(1/\varepsilon)\,U_d\!\big(2/\gamma^2\varepsilon\big)\big(d^2+T_{\lfloor d/2\rfloor}(\gamma^2\varepsilon/2)\big)\quad(d\ge2),\qquad T_1(\varepsilon)\le C_0\log_2(1/\varepsilon),$$
--   where $U_d(a)=1+130^k\binom{h+k}{k}$ with $k=1+\lceil\log_{4/3}(4d^2)\rceil$, $h=\lceil\log_2a\rceil$. Then for every $d\ge2$ and $\varepsilon\in(0,1/4]$
--   $$T_d(\varepsilon)\le\big(\log(1/(\gamma\varepsilon))\big)^{C\log^2d}.$$
--   This is the final computation of the proof of Theorem 1.
--
--   Differences from the source:
--   - reading: the chain of inequalities (16), with 'C a universal constant that may change from line to line' → an implication from the recurrence (constant C₀) to the bound (constant C depending only on C₀); reason: the derivation's content; T is any function obeying the recurrence
--   - reading: U_d(a) 'bounds one plus the number of boosting rounds' → U_d(a) = 1 + 130^k C(h+k, k) with Lemma 5's k, h at n = 2d, B± = 2d; reason: the bound the proof inserts
--   - encoding: log₂ and log; log² d → Real.logb 2 and Real.log; (Real.log d)^2; reason: Lean names; the final log is natural
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), proof of Theorem 1, recurrence and display (16), p.21

import Mathlib
import Definitions.Def_LinfContractionFP_roundsBound

namespace LinfContractionFP

/-- The recurrence of the proof of Theorem 1 and display (16): if `T_d(ε)` satisfies
`T_d(ε) ≤ C₀ d² log₂(1/ε) U_d(2/(γ²ε)) (d² + T_{⌊d/2⌋}(γ²ε/2))` for `d ≥ 2` and
`T_1(ε) ≤ C₀ log₂(1/ε)`, for all `ε ∈ (0, 1/4]`, with `U_d(a) = 1 + 130^k C(h+k, k)` the bound of
Lemma 5 for Label in dimension `d` (`k = 1 + ⌈log_{4/3}(4d²)⌉`, `h = ⌈log₂ a⌉`), then
`T_d(ε) ≤ (log(1/(γε)))^{C log² d}` for a constant `C` depending only on `C₀`.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), proof of Theorem 1, p.21: "we can write a recurrence for the total number of arithmetic
operations, comparisons, and exact evaluations of f performed by Solve(f, ε):
T_d(ε) ≤ C d² log₂(1/ε) U_d(2/γ²ε)(d² + T_{⌊d/2⌋}(γ²ε/2)), T_1(ε) ≤ C log₂(1/ε). where U_d(a)
bounds one plus the number of boosting rounds. [...] iterating the recurrence gives
T_d(ε) ≤ C (d² r ℓ)^r r ℓ ∏_{t=1}^r (Crℓ/t)^{Ct} ≤ C 2^{r²} ℓ^{C r²} ≤ ℓ^{C r²}
≤ log(1/(γε))^{C log² d}, (16) where we used the fact that γε ≤ 1/4 to absorb terms into a large
exponent constant C."

**Formalization Note.** `log₂` is `Real.logb 2`; the final `log` is the natural logarithm and
`log² d = (log d)²`. `T` is any function satisfying the recurrence (for one fixed `γ`); `⌊d/2⌋`
is natural-number division. The constant `C₀` of the recurrence is the paper's universal `C`;
the conclusion's `C` depends on `C₀` only, not on `γ`, `T`, `d` or `ε`. `U_d` is
`roundsBound d`. -/
theorem eq_16 : ∀ C₀ : ℝ, 0 < C₀ → ∃ C : ℝ, ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
    ∀ T : ℕ → ℝ → ℝ,
      (∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
        T d ε ≤ C₀ * (d : ℝ) ^ 2 * Real.logb 2 (1 / ε) * roundsBound d (2 / (γ ^ 2 * ε)) *
          ((d : ℝ) ^ 2 + T (d / 2) (γ ^ 2 * ε / 2))) →
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → T 1 ε ≤ C₀ * Real.logb 2 (1 / ε)) →
      ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
        T d ε ≤ Real.log (1 / (γ * ε)) ^ (C * Real.log d ^ 2) := by sorry

end LinfContractionFP
