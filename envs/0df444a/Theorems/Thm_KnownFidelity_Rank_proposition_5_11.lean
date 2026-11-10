-- Prove2me | Theorems.Thm_KnownFidelity_Rank_proposition_5_11
-- name    : KnownFidelity.Rank.proposition_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:52:26.618919+00:00
-- url     : https://prove2.me/theorems/188ee549-c92b-4156-9746-4fc41a355b89
-- title:
--   Proposition 5.11 — Cauchy cancellation bound $d_{\mathrm{tr}}(\overline\Psi_0^{(m)},\overline\Psi_1^{(m)})\le[2m\theta^K/((K+1)(1-\theta))]^{1/2}$
-- statement:
--   Let $a^{(0)},a^{(1)}\in\mathbb R^r_{\ge0}$ with $\sum_ia^{(b)}_i=1$, let $m\ge1$, and let $\overline\Psi_b^{(m)}$ be the $m$-copy average pure state of the size-biased Wishart prior built from $a^{(b)}$ (Eqs. (40)–(43)). Assume
--
--   $$u_{0,k}=u_{1,k}\quad(1\le k\le K),\qquad \max_{b,i}a^{(b)}_i\le B/r .$$
--
--   If $\theta=mB^2/r^2<1$, then
--
--   $$d_{\mathrm{tr}}\big(\overline\Psi_0^{(m)},\overline\Psi_1^{(m)}\big)\ \le\ \Big[\frac{2m\theta^K}{(K+1)(1-\theta)}\Big]^{1/2}.$$
--
--   Matching the first $K$ power sums makes the two averaged experiments nearly indistinguishable: only permutations with a cycle longer than $K$ see the difference.
--
--   Differences from the source:
--   - generalization: the vectors a^{(0)}, a^{(1)} supplied by Proposition 5.2 (§5.4) → any nonnegative vectors with Σ_i a^{(b)}_i = 1 and the stated hypotheses; (31)–(32) not assumed; reason: the proof uses only (28), the moment matching and the entry bound; the paper's vectors satisfy these, so the statement specializes to the source
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Proposition 5.11, p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_PsiAvg
import Definitions.Def_KnownFidelity_Rank_powerSum
import Definitions.Def_KnownFidelity_Rank_traceDist

namespace KnownFidelity.Rank

/-- **Proposition 5.11 (Cauchy cancellation bound).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Proposition 5.11, printed p. 21 (PDF p. 23): "Assume u_{0,k} = u_{1,k}, 1 ≤ k ≤ K, and
max_{b,i} a^{(b)}_i ≤ B/r. If θ = mB²/r² < 1, then
d_tr(Ψ̄_0^{(m)}, Ψ̄_1^{(m)}) ≤ [2mθ^K/((K + 1)(1 − θ))]^{1/2}. (63)"

For nonnegative `a^{(0)}, a^{(1)} ∈ ℝ^r` summing to `1` (the standing assumptions of §5.4), an
integer `m ≥ 1`, power sums equal for `1 ≤ k ≤ K` and all entries at most `B/r`, if
`θ = mB²/r² < 1` then the trace distance between the `m`-copy averages `Ψ̄_b^{(m)}` of Eq. (43)
is at most `√(2mθ^K/((K+1)(1−θ)))`.

**Formalization Note.** `Ψ̄_b^{(m)} = PsiAvg a^{(b)} m` (size-biased Wishart prior (41), unit
vector (42), average (43)); `d_tr = traceDist`. The vectors are any vectors with these
hypotheses; properties (31)–(32) of Proposition 5.2 are not assumed (the proof does not use
them). -/
theorem proposition_5_11 {r m K : ℕ} (a₀ a₁ : Fin r → ℝ) (ha₀ : ∀ i, 0 ≤ a₀ i)
    (ha₁ : ∀ i, 0 ≤ a₁ i) (hs₀ : ∑ i, a₀ i = 1) (hs₁ : ∑ i, a₁ i = 1) (hm : 1 ≤ m)
    (hmatch : ∀ k : ℕ, 1 ≤ k → k ≤ K → powerSum a₀ k = powerSum a₁ k)
    (B : ℝ) (hB : ∀ i, a₀ i ≤ B / r ∧ a₁ i ≤ B / r) (hθ : m * B ^ 2 / r ^ 2 < 1) :
    traceDist (PsiAvg a₀ m) (PsiAvg a₁ m) ≤
      Real.sqrt (2 * m * (m * B ^ 2 / r ^ 2) ^ K / ((K + 1) * (1 - m * B ^ 2 / r ^ 2))) := by sorry

end KnownFidelity.Rank
