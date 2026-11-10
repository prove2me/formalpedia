-- Prove2me | Theorems.Thm_KnownFidelity_Rank_proposition_5_2
-- name    : KnownFidelity.Rank.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:46:52.688753+00:00
-- url     : https://prove2.me/theorems/d72fed76-e38d-4260-9484-0471ec2a7ba7
-- title:
--   Proposition 5.2 — exact moment-matched pair of spectra
-- statement:
--   There are universal constants $0<c_0<c_1$ with the following property. For every fixed $0<\eta_0<1/10$ there is a constant $C_{\eta_0}$ such that, whenever $K\ge2$ and
--
--   $$r\ \ge\ C_{\eta_0}K^7\log^2(K+2),$$
--
--   there are vectors $a^{(0)},a^{(1)}\in\mathbb R^r_{\ge0}$ satisfying
--
--   1. $\sum_i a^{(b)}_i=1$ for $b=0,1$;
--   2. $\sum_i (a^{(0)}_i)^k=\sum_i (a^{(1)}_i)^k$ for $1\le k\le K$;
--   3. $\max_{b,i}a^{(b)}_i\le C_{\eta_0}K^2/r$;
--   4. $\#\{i:\ a^{(0)}_i>0\}\le\eta_0 r$;
--   5. $\#\{i:\ c_0/r\le a^{(1)}_i\le c_1/r\}\ge r/2$.
--
--   These two spectra, one supported on few coordinates and one spread out, with identical low-order moments, are the seeds of the hard instances of Proposition 4.1. Logarithms are natural.
--
--   Differences from the source:
--   - encoding: a constant C_{η₀} (sign unstated) → ∃ C : ℝ with no sign condition, before K and r; reason: a nonpositive C is impossible anyway: at r = 0 no vector sums to 1, so the existential forces the paper's positive constant
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Proposition 5.2, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_powerSum

namespace KnownFidelity.Rank

/-- **Proposition 5.2 (Exact moment-matched pair).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Proposition 5.2, printed p. 12 (PDF p. 14): "There are universal constants 0 < c₀ < c₁
with the following property. For every fixed 0 < η₀ < 1/10 there is a constant C_{η₀} such that,
whenever K ≥ 2 and r ≥ C_{η₀} K⁷ log²(K + 2), (27) there are vectors a^{(0)}, a^{(1)} ∈ R^r_+
satisfying Σ_i a^{(b)}_i = 1, (28) Σ_i (a^{(0)}_i)^k = Σ_i (a^{(1)}_i)^k, 1 ≤ k ≤ K, (29)
max_{b,i} a^{(b)}_i ≤ C_{η₀} K²/r, (30) #{i : a^{(0)}_i > 0} ≤ η₀ r, (31)
#{i : c₀/r ≤ a^{(1)}_i ≤ c₁/r} ≥ r/2. (32)"

**Formalization Note.** `c₀, c₁` come first (universal), then `C_{η₀}` after `η₀` and before
`K, r`. `R^r_+` is `Fin r → ℝ` with nonnegative entries; `log` is natural (§2); (28) and (30) are
required for both `b = 0, 1`; the cardinalities are those of `Finset.univ.filter`, compared in
`ℝ`. -/
theorem proposition_5_2 :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ c₀ < c₁ ∧
      ∀ η₀ : ℝ, 0 < η₀ → η₀ < 1 / 10 → ∃ C : ℝ, ∀ K : ℕ, 2 ≤ K → ∀ r : ℕ,
        C * (K : ℝ) ^ 7 * Real.log (K + 2) ^ 2 ≤ r →
        ∃ a₀ a₁ : Fin r → ℝ, (∀ i, 0 ≤ a₀ i) ∧ (∀ i, 0 ≤ a₁ i) ∧
          ∑ i, a₀ i = 1 ∧ ∑ i, a₁ i = 1 ∧
          (∀ k : ℕ, 1 ≤ k → k ≤ K → powerSum a₀ k = powerSum a₁ k) ∧
          (∀ i, a₀ i ≤ C * (K : ℝ) ^ 2 / r ∧ a₁ i ≤ C * (K : ℝ) ^ 2 / r) ∧
          ((Finset.univ.filter fun i => 0 < a₀ i).card : ℝ) ≤ η₀ * r ∧
          (r : ℝ) / 2 ≤
            ((Finset.univ.filter fun i => c₀ / r ≤ a₁ i ∧ a₁ i ≤ c₁ / r).card : ℝ) := by sorry

end KnownFidelity.Rank
