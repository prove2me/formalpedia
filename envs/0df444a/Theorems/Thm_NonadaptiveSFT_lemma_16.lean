-- Prove2me | Theorems.Thm_NonadaptiveSFT_lemma_16
-- name    : NonadaptiveSFT.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:34.178962+00:00
-- url     : https://prove2.me/theorems/7ea903c5-e5a2-40a4-9449-03f8d7061f90
-- title:
--   Lemma 16 — validity before the first failure: nested supports in $\Omega$, valid norm promises, and $\sum_{i\le n}\kappa_i<30838s<K$
-- statement:
--   Assume the standing assumptions of §6: $2\le s<N$, $\tau\ge0$ and $\sigma_s(\widehat X)_2^2\le s\tau^2$. Suppose the least-squares sample $U$ lies in the event of Lemma 14, let $n\ge1$, and suppose the recovery algorithm reaches round $n$ and calls $1,\dots,n-1$ all succeeded. Then:
--
--   1. $S_1\subseteq S_2\subseteq\dots\subseteq S_n\subseteq\Omega$;
--   2. $T_n>0$, $T_{min}\le T_n\le M_{S_n}$, and $\|\widehat X-C_{S_n}\|_2\le M_{S_n}$, so call $n$ receives a valid norm promise;
--   3. the ratios of the first $n$ rounds satisfy
--
--   $$\sum_{i=1}^n\kappa_i<30838s<K.\tag{39}$$
--
--   Item 3 is what keeps the total locator budget, and hence the query and work bounds, linear in $s$.
--
--   **Formalization Note** The statement holds for every sequence of locator outcomes, not only for those of the paper's locator.
--
--   Differences from the source:
--   - generalization: the algorithm with its locator → the loop of §6.1 with an arbitrary sequence of locator outcomes; reason: the lemma's hypotheses and proof concern only the outcomes of calls 1, …, n − 1; the paper's locator is one such sequence
--   - reading: the event of Lemma 14 → LSGood: for every S ⊆ Ω, A_S^*A_S nonsingular and (28), (29); reason: the event as stated in Lemma 14, with the nonsingularity its proof provides
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Lemma 16, p.35 (PDF p.37); standing assumptions and (36), p.33

import Mathlib
import Definitions.Def_NonadaptiveSFT_Recovery

namespace NonadaptiveSFT

/-- **Lemma 16** (Validity before the first failure), p.35 (PDF p.37).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…); standing assumptions of §6 (p.33): `2 ≤ s < N`, `τ ≥ 0`,
(33) `σ_s(X̂)₂² ≤ sτ²`, constants (36).

Suppose the least-squares sample `U` falls into the event of Lemma 14. Let `n ≥ 1`, and suppose the
algorithm reaches round `n` and calls `1, …, n − 1` all succeeded. Then:
1. `S_1 ⊆ S_2 ⊆ ⋯ ⊆ S_n ⊆ Ω`;
2. `T_n > 0`, `T_min ≤ T_n ≤ M_{S_n}`, and `‖X̂ − C_{S_n}‖₂ ≤ M_{S_n}`;
3. `Σ_{i=1}^n κ_i < 30838s < K` (39).

**Formalization Note.** The algorithm is the loop of §6.1 (`NonadaptiveSFT.loopAt`) run with an
**arbitrary** sequence `loc` of locator outcomes, so the lemma holds for every locator. "The event of
Lemma 14" is `LSGood X U s τ` (for every `S ⊆ Ω`: `A_S^*A_S` nonsingular, (28), (29)). Round `i` and
call `i` are as on p.34: `S_i`, `T_i`, `κ_i = M_{S_i}²/T_i²` are read from the state after round
`i − 1`. `T_min = τ/2`, `K = 31000s`. -/
theorem lemma_16 (a d : ℕ) (ha : 1 ≤ a) (hd : 1 ≤ d) (s : ℕ) (hs : 2 ≤ s)
    (hsN : s < 2 ^ (a * d)) (τ : ℝ) (hτ : 0 ≤ τ) (X : G a d → ℂ)
    (h33 : sigma (lexKey a d) s (hat X) ^ 2 ≤ s * τ ^ 2)
    (U : Fin (nls s) → G a d) (hU : LSGood X U s τ) (loc : ℕ → Option (Finset (G a d)))
    (n : ℕ) (hn : 1 ≤ n) (hreach : RoundReached X U s τ loc n)
    (hsucc : ∀ i, 1 ≤ i → i < n → CallSucceeds X U s τ loc i) :
    ((∀ i, 1 ≤ i → i < n → roundS X U s τ loc i ⊆ roundS X U s τ loc (i + 1)) ∧
      roundS X U s τ loc n ⊆ Omega X τ) ∧
    (0 < roundT X U s τ loc n ∧ τ / 2 ≤ roundT X U s τ loc n ∧
      roundT X U s τ loc n ≤ Mval X U (roundS X U s τ loc n) (Real.sqrt s * τ) ∧
      l2 (hat X - fit X U (roundS X U s τ loc n)) ≤
        Mval X U (roundS X U s τ loc n) (Real.sqrt s * τ)) ∧
    (∑ i ∈ Finset.Icc 1 n, roundKappa X U s τ loc i < 30838 * (s : ℝ) ∧
      30838 * (s : ℝ) < (Kbud s : ℝ)) := by sorry

end NonadaptiveSFT
