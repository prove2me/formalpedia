-- Prove2me | Theorems.Thm_KnownFidelity_Rank_corollary_5_12
-- name    : KnownFidelity.Rank.corollary_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:52:35.750542+00:00
-- url     : https://prove2.me/theorems/918d0844-8c13-4b37-8617-ec5967742272
-- title:
--   Corollary 5.12 — base indistinguishability: $d_{\mathrm{tr}}(\overline\Psi_0^{(m)},\overline\Psi_1^{(m)})\le 4r^{-1/2}$, $m\ge cr^2/\log^4(r+2)$
-- statement:
--   Fix $\theta_0=1/2$, $K=\lfloor 5\log(r+2)\rfloor$, an entry-bound constant $C_B>0$, $B=C_BK^2$, and
--
--   $$m=\Big\lfloor\theta_0\,\frac{r^2}{B^2}\Big\rfloor .$$
--
--   Then there are $c>0$ and $r_1$ such that for every $r\ge r_1$ and every pair $a^{(0)},a^{(1)}\in\mathbb R^r_{\ge0}$ with $\sum_ia^{(b)}_i=1$, equal power sums for $1\le k\le K$ and all entries at most $B/r$,
--
--   $$d_{\mathrm{tr}}\big(\overline\Psi_0^{(m)},\overline\Psi_1^{(m)}\big)\le 4r^{-1/2},\qquad m\ \ge\ c\,\frac{r^2}{\log^4(r+2)} .$$
--
--   With the vectors of Proposition 5.2 ($C_B=C_{\eta_0}$) this is the base pair of priors from which Proposition 4.1 is built: their $m$-copy experiments are indistinguishable with $m$ of order $r^2$ up to logarithms. Logarithms are natural.
--
--   Differences from the source:
--   - reading: for the priors Π^{(m)}_b constructed above (the size condition (27) holds for all large r; c = c(η₀)) → ∀ C_B > 0, ∃ c > 0, ∃ r₁, ∀ r ≥ r₁; reason: the text's own 'for all large r' and 'a constant c = c(η₀)'; C_{η₀} enters only through the entry bound B = C_{η₀}K²
--   - generalization: the vectors a^{(0)}, a^{(1)} of Proposition 5.2 → every pair of nonnegative vectors with (28), (29) up to K and (30) with constant C_B; (31)–(32) not assumed; reason: the proof uses only these properties; the paper's vectors satisfy them
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §5.5, Eqs. (64)–(65) and Corollary 5.12, p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_PsiAvg
import Definitions.Def_KnownFidelity_Rank_powerSum
import Definitions.Def_KnownFidelity_Rank_traceDist

namespace KnownFidelity.Rank

/-- **Corollary 5.12 (Base indistinguishability).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §5.5, Eqs. (64)–(65) and Corollary 5.12, printed p. 22 (PDF p. 24): "Fix θ₀ = 1/2,
K = ⌊5 log(r + 2)⌋, (64) let B = C_{η₀} K² be the entry bound from proposition 5.2, and put
m = ⌊θ₀ r²/B²⌋. (65) … Corollary 5.12 (Base indistinguishability). For the priors Π_b^{(m)}
constructed above, with m given by (65), d_tr(Ψ̄_0^{(m)}, Ψ̄_1^{(m)}) ≤ 4r^{−1/2},
m ≥ c r²/log⁴(r + 2)."

For every entry-bound constant `C_B > 0` there are `c > 0` and `r₁` such that for every `r ≥ r₁`,
with `K = ⌊5 log(r+2)⌋`, `B = C_B K²` and `m = ⌊r²/(2B²)⌋`, and for **every** pair of
nonnegative vectors `a^{(0)}, a^{(1)} ∈ ℝ^r` summing to `1`, with equal power sums for
`1 ≤ k ≤ K` and entries at most `B/r`: `d_tr(Ψ̄_0^{(m)}, Ψ̄_1^{(m)}) ≤ 4/√r` and
`m ≥ c r²/log⁴(r+2)`.

**Formalization Note.** "For the priors constructed above" is read as: for every pair of vectors
with the properties the construction uses ((28)–(30)); (31)–(32) are not assumed. The constant
`C_{η₀}` of Proposition 5.2 is the arbitrary `C_B`, so `c = c(η₀)` becomes `c = c(C_B)`. "The
size condition (27) holds for all large r" is the threshold `r₁`. `θ₀ = 1/2` is written in;
`log` is natural. -/
theorem corollary_5_12 (CB : ℝ) (hCB : 0 < CB) :
    ∃ c : ℝ, 0 < c ∧ ∃ r₁ : ℕ, ∀ r : ℕ, r₁ ≤ r →
      let K : ℕ := ⌊5 * Real.log (r + 2)⌋₊
      let B : ℝ := CB * (K : ℝ) ^ 2
      let m : ℕ := ⌊(1 / 2 : ℝ) * (r : ℝ) ^ 2 / B ^ 2⌋₊
      ∀ a₀ a₁ : Fin r → ℝ, (∀ i, 0 ≤ a₀ i) → (∀ i, 0 ≤ a₁ i) →
        ∑ i, a₀ i = 1 → ∑ i, a₁ i = 1 →
        (∀ k : ℕ, 1 ≤ k → k ≤ K → powerSum a₀ k = powerSum a₁ k) →
        (∀ i, a₀ i ≤ B / r ∧ a₁ i ≤ B / r) →
        traceDist (PsiAvg a₀ m) (PsiAvg a₁ m) ≤ 4 / Real.sqrt r ∧
          c * (r : ℝ) ^ 2 / Real.log (r + 2) ^ 4 ≤ m := by sorry

end KnownFidelity.Rank
