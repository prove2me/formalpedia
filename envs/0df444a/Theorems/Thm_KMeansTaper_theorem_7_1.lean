-- Prove2me | Theorems.Thm_KMeansTaper_theorem_7_1
-- name    : KMeansTaper.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:24.321197+00:00
-- url     : https://prove2.me/theorems/ea5184c1-29e3-4127-a878-630996be90db
-- title:
--   Theorem 7.1 — deterministic additive approximation, squared
-- statement:
--   Let $\kappa>0$ be rational and $0<c\le1$ real with $\mathrm{SFI}(\kappa,c)$ and $1+\kappa/e\le4.04$. Then:
--
--   1. for every $\varepsilon>0$ there are $c_\varepsilon\in\mathbb N$ and a deterministic polynomial-time algorithm, a Turing machine (`Turing.TM2ComputableInPolyTime`, every tape alphabet finite) running in time polynomial in the input length on the published instance code, which on every instance opens a nonempty set $S\subseteq F$ with $|S|\le k+c_\varepsilon$ and
--   $$\mathrm{cost}_2(S)\le\Bigl(1+\frac{\kappa}{e}+\varepsilon\Bigr)\mathrm{LP}_2;$$
--   2. $\mathrm{LP}_2\le\mathrm{OPT}_k$ on every instance.
--
--   Together these give the chain $\mathrm{cost}_2\le(1+\kappa/e+\varepsilon)\mathrm{LP}_2\le(1+\kappa/e+\varepsilon)\mathrm{OPT}_k$: the first two stages of the algorithm round the LP with a constant number of extra centers.
--
--   **Formalization Note** The output is the indicator list of $S$; $4.04$ is the exact rational $404/100$.
--
--   Differences from the source:
--   - reading: "Under SFI(κ, c)" with κ, c otherwise unqualified → κ rational, c real, 0 < κ and 0 < c ≤ 1; reason: the proof is Corollary A.17, which applies Theorem D.17 (rational κ > 0, 0 < c ≤ 1); these are implicit hypotheses of the printed statement (c ≤ 1 is also the standing assumption of Proposition 4.1(iii) and Section 5.2; 0 < κ follows from SFI by Proposition 4.1(i))
--   - encoding: a deterministic polynomial-time algorithm opening ≤ k + c_ε facilities → a Turing.TM2ComputableInPolyTime machine with finite alphabets over encodeInstance whose output is the indicator list of a nonempty S ⊆ F (CorrectAdditive); reason: Lean model; the empty set has infinite cost in the paper
--   - encoding: LP2, the LP of [35, (2.1)] with squared objective → lp2, the standard k-median relaxation with squared distances; reason: the cited LP is not printed in the paper
--   - encoding: the chain cost2 ≤ (1 + κ/e + ε) LP2 ≤ (1 + κ/e + ε) OPT_k → two conjuncts: the first inequality and LP2 ≤ OPT_k; reason: the second inequality of the chain follows from LP2 ≤ OPT_k
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorem 7.1, p.17 (PDF p.20); proof via Corollary A.17, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_cost2
import Definitions.Def_KMeansTaper_SFI
import Definitions.Def_KMeansTaper_lp2

namespace KMeansTaper

open OAI.MetricKMedian (Instance encodeInstance)

/-- **Theorem 7.1 (deterministic additive approximation, squared)**, p.17 (PDF p.20).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

Under `SFI(κ, c)` with `1 + κ/e ≤ 4.04`, for every `ε > 0` there are `c_ε ∈ ℕ` and a
deterministic polynomial-time algorithm opening `≤ k + c_ε` facilities with
`cost₂ ≤ (1 + κ/e + ε) LP₂ ≤ (1 + κ/e + ε) OPT_k`.

**Formalization Note.** `κ ∈ ℚ`, `0 < κ` and `0 < c ≤ 1` (`c` real) are the hypotheses of Theorem D.17,
through which the proof (Corollary A.17) runs. "Deterministic polynomial-time algorithm" is a
`Turing.TM2ComputableInPolyTime` machine with finite alphabets over the published
`encodeInstance`; the output is the indicator bit-list of the opened set. The second conjunct is
the last inequality of the chain, `LP₂ ≤ OPT_k`. -/
theorem theorem_7_1 (κ : ℚ) (c : ℝ) (hκ : 0 < κ) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hκe : 1 + (κ : ℝ) / Real.exp 1 ≤ 404 / 100) (hSFI : SFI κ c) :
    (∀ ε : ℝ, 0 < ε → ∃ cε : ℕ,
      ∃ (algorithm : Instance → List Bool)
        (M : Turing.TM2ComputableInPolyTime encodeInstance id algorithm),
        (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
        ∀ I, CorrectAdditive (1 + κ / Real.exp 1 + ε) cε I (algorithm I)) ∧
    ∀ I : Instance, lp2 I ≤ optimum2 I := by sorry

end KMeansTaper
