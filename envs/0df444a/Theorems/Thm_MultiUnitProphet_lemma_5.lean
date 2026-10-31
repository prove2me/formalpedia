-- Prove2me | Theorems.Thm_MultiUnitProphet_lemma_5
-- name    : MultiUnitProphet.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:09.608426+00:00
-- url     : https://prove2.me/theorems/4c1ba2d0-ac1f-4b50-920b-5ae41aef1054
-- title:
--   Lemma 5 — (GenBern : $\min\mu$ s.t. $\delta=\phi$) has a minimizer whose non-degenerate biases are equal
-- statement:
--   Let $0<k<n$. There are biases $b\in[0,1]^n$ with $\delta_k(X)=\phi^\star_k(n)$ for $X=\sum_t\mathrm{Bernoulli}(b_t)$ such that
--
--   1. $\mu_k(X)$ is the minimum of (GenBern : $\min\mu$ s.t. $\delta=\phi$), and
--   2. all biases in $(0,1)$ are equal.
--
--   The minimizer may still contain degenerate Bernoullis (bias $0$ or $1$); Lemma 6 removes them.
--
--   Differences from the source:
--   - reading: the program is minimized when all non-degenerate Bernoulli distributions have equal bias → there exists a minimizer whose biases in (0, 1) are all equal; reason: the proof selects one optimal solution; not every minimizer has equal non-degenerate biases (k = 1: every b with ∏(1 − b_t) = φ⋆ is optimal)
--   - reading: X is the sum of Bernoulli r.v.s (no count given) → n Bernoullis, the same n as in (GenBern : min φ s.t. δ = µ = φ); reason: the programs of §5 are posed for one instance size
--   - encoding: a supply k > 0 and n > k (Lemma 3) → 0 < k < n; reason: the setting of Lemma 3
--   - encoding: X a sum of independent Bernoullis with biases b_t → deltaPB k b and muPB k b, finite sums over the pmf CommitteeVoting.SingleVoter.pbPMF b univ j, with b t ∈ [0, 1]; reason: the Poisson-binomial law written through its pmf; same values
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, Lemma 5, p.11 (proof p.12)

import Mathlib
import Definitions.Def_MultiUnitProphet_GenBern

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **Lemma 5: (GenBern : min µ s.t. δ = φ) has a minimizer whose non-degenerate biases are all
equal.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, Lemma 5, p.11 (proof p.12): "The optimization problem (GenBern : min µ s.t. δ = ϕ) is
minimized when all non-degenerate Bernoulli distributions (that do not have bias 0 or 1) have equal
bias."

For `0 < k < n` there are biases `b ∈ [0,1]ⁿ` with `δ_k(X) = φ⋆_k(n)` such that `µ_k(X)` is the
least value of (GenBern : min µ s.t. δ = φ) and all biases in `(0, 1)` are equal.

**Formalization Note.** "Is minimized when" is read as the existence of such a minimizer (not
every minimizer has the property). The number of Bernoullis is the same `n` as in
(GenBern : min φ s.t. δ = µ = φ). -/
theorem lemma_5 (k n : ℕ) (hk : 0 < k) (hkn : k < n) :
    ∃ b : Fin n → ℝ, (∀ t, b t ∈ Set.Icc (0 : ℝ) 1) ∧ deltaPB k b = phiStar k n ∧
      IsLeast (genBernMuValues k n (phiStar k n)) (muPB k b) ∧
      ∀ s t, b s ∈ Set.Ioo (0 : ℝ) 1 → b t ∈ Set.Ioo (0 : ℝ) 1 → b s = b t := by sorry

end MultiUnitProphet
