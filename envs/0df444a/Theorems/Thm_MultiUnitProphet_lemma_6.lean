-- Prove2me | Theorems.Thm_MultiUnitProphet_lemma_6
-- name    : MultiUnitProphet.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:14:19.988741+00:00
-- url     : https://prove2.me/theorems/db21d354-eb1c-4407-9b3c-b813f6f43bd3
-- title:
--   Lemma 6 — (GenBern : $\min\mu$ s.t. $\delta=\phi$) is minimized by $n$ equal non-degenerate biases
-- statement:
--   Let $0<k<n$. There is $c\in(0,1)$ such that the sum $X$ of $n$ independent Bernoullis of bias $c$ satisfies $\delta_k(X)=\phi^\star_k(n)$ and $\mu_k(X)$ is the minimum of (GenBern : $\min\mu$ s.t. $\delta=\phi$).
--
--   With Lemma 4 this identifies the worst case for $n$ buyers as a binomial with equal biases, the starting point of the Poisson limit in §5.4.
--
--   Differences from the source:
--   - reading: the program is minimized when all of the Bernoulli distributions have equal bias (and there are no degenerate distributions) → there exists a minimizer with all n biases equal to some c ∈ (0, 1); reason: existence of such a minimizer is what the proof shows and what §5.4 uses
--   - reading: X is the sum of Bernoulli r.v.s (no count given) → n Bernoullis, the same n as in (GenBern : min φ s.t. δ = µ = φ); reason: the programs of §5 are posed for one instance size
--   - encoding: a supply k > 0 and n > k (Lemma 3) → 0 < k < n; reason: the setting of Lemma 3
--   - encoding: X a sum of independent Bernoullis with biases b_t → deltaPB k b and muPB k b, finite sums over the pmf CommitteeVoting.SingleVoter.pbPMF b univ j, with b t ∈ [0, 1]; reason: the Poisson-binomial law written through its pmf; same values
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, Lemma 6, p.15 (proof pp.15–16)

import Mathlib
import Definitions.Def_MultiUnitProphet_GenBern

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **Lemma 6: (GenBern : min µ s.t. δ = φ) is minimized by equal non-degenerate biases.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, Lemma 6, p.15 (proof pp.15–16): "The optimization problem (GenBern : min µ s.t. δ = ϕ) is
minimized when all of the Bernoulli distributions have equal bias (and there are no degenerate
distributions)."

For `0 < k < n` there is `c ∈ (0, 1)` such that the sum `X` of `n` independent Bernoullis of bias
`c` has `δ_k(X) = φ⋆_k(n)` and `µ_k(X)` is the least value of (GenBern : min µ s.t. δ = φ).

**Formalization Note.** Read as the existence of such a minimizer, with the same `n` as in
(GenBern : min φ s.t. δ = µ = φ). -/
theorem lemma_6 (k n : ℕ) (hk : 0 < k) (hkn : k < n) :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, deltaPB k (fun _ : Fin n => c) = phiStar k n ∧
      IsLeast (genBernMuValues k n (phiStar k n)) (muPB k (fun _ : Fin n => c)) := by sorry

end MultiUnitProphet
