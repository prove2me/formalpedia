-- Prove2me | Theorems.Thm_NashAmplification_Filtering_lemma_B_1
-- name    : NashAmplification.Filtering.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:23:24.737282+00:00
-- url     : https://prove2.me/theorems/4c78f4bc-81fe-4b2e-940d-9dbd6df68990
-- title:
--   Lemma B.1 — exact computation of one filtering round
-- statement:
--   A rational input supplies $n\ge1$ entries of each of $\rho,w,v$, together with $q,h$. Assume $\rho\ge0$, $w,v\in[0,1]$, $0<q<1$, $h>0$ and $\sum_z\rho(z)w(z)>0$. There exist an absolute constant $c>0$ and one deterministic polynomial-time machine returning a rational threshold and all $n$ updated weights, exactly equal to the real Filter and its smallest threshold.
--
--   For any $\ell_{\rm in}\ge1$ bounding the encoded length of every supplied rational, including $q,h$,
--   $$\text{each output rational length}\le cn(\ell_{\rm in}+1),\qquad\text{total output length}\le cn^2(\ell_{\rm in}+1).$$
--   Taking $n=|A|^t$ gives both output-bit bounds in the source. The algorithmic guarantee and exact equality cover all weights, including those at zero mass. The output constant and machine are chosen before any input.
--
--   Differences from the source:
--   - generalization: n=|A|^t and fixed admissible q,h → arbitrary n≥1 with q,h supplied to one machine, total also on invalid rational data; reason: the exact-arithmetic algorithm is uniform in the list size and parameters; correctness is required only under the source conditions
--   - encoding: binary rational encodings and polynomial bit operations → explicit framed binary words, signed reduced threshold output, and FinTM2 steps; reason: the fixed finite-alphabet machine model and bit operations are polynomially related; framing adds only constant overhead per entry
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, Lemma B.1, PDF p. 29 (printed p. 28)

import Definitions.Def_NashAmplification_Filtering_Encoding
import Definitions.Def_NashAmplification_Filtering_Filter

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Lemma B.1, PDF 29: one fixed machine, absolute output-bit constants,
and exact agreement with the real Filter, including its smallest threshold. -/
theorem lemma_B_1 :
    ∃ c : ℕ, 0 < c ∧
    ∃ compute : RoundInput → ℚ × List RawRat,
      Nonempty (Turing.TM2ComputableInPolyTime encRound encRoundOutput compute) ∧
      ∀ d : RoundInput,
        d.q.value ∈ Set.Ioo (0 : ℝ) 1 → 0 < d.h.value →
        (∀ i, d.weight i ∈ Set.Icc (0 : ℝ) 1) →
        (∀ i, d.assigned i ∈ Set.Icc (0 : ℝ) 1) →
        0 < mass d.rho d.weight →
        (compute d).2.length = d.n ∧
        ((compute d).1 : ℝ) = threshold d.q.value d.h.value d.rho d.weight d.assigned ∧
        (∀ i : Fin d.n, ((compute d).2.getD i.val zeroRat).value =
          filterWeights d.q.value d.h.value d.rho d.weight d.assigned i) ∧
        ∀ ℓ : ℕ, 1 ≤ ℓ →
          (∀ a ∈ [d.q,d.h] ++ d.ρ ++ d.w ++ d.v, (encRaw a).length ≤ ℓ) →
          (encSigned (compute d).1).length ≤ c * d.n * (ℓ+1) ∧
          (∀ a ∈ (compute d).2, (encRaw a).length ≤ c * d.n * (ℓ+1)) ∧
          (encRoundOutput (compute d)).length ≤ c * d.n^2 * (ℓ+1) := by sorry
end NashAmplification.Filtering
