-- Prove2me | Theorems.Thm_HypergraphUnreliability_FPRAS_lemma_9_3
-- name    : HypergraphUnreliability.FPRAS.lemma_9_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:16.5202+00:00
-- url     : https://prove2.me/theorems/f75c6166-1ea5-4b2d-8de4-b753368b2d22
-- title:
--   Lemma 9.3 — Rational relative exponential normalization
-- statement:
--   For rational $\Lambda\in[0,R]$ and rational $\varepsilon\in(0,1)$, a positive rational $q_0$ satisfying
--   $$\Bigl|\frac{q_0}{e^{-\Lambda}}-1\Bigr|\le\frac{\varepsilon}{64}$$
--   can be computed in time polynomial in the bit encodings, the numerical bound $R+1$, and $\log(1/\varepsilon)$.
--
--   The dependence on $R$ is through its value, not its bit length; (9.3) makes this polynomial in the application. The case $\Lambda=0$ is included.
--
--   **Formalization Note** The size is the encoding length of $(\Lambda,R,\varepsilon)$ plus $\lceil R\rceil+1$. The encoding of $\varepsilon$ bounds $\log(1/\varepsilon)$.
--
--   Differences from the source:
--   - encoding: polynomial time in the bit model → one fixed Mathlib `Turing.FinTM2` with finite alphabets and one fixed polynomial bounding its steps, chosen before the inputs; reason: a `FinTM2` step executes a bounded program fragment on a finite alphabet, so steps and bit operations agree up to a constant factor; every instance of the claim is kept
-- source:
--   Zhijie Zheng, STOC 2027 submission #37 (October 2026), Lemma 9.3, p. 15

import Mathlib
import Definitions.Def_HypergraphUnreliability_FPRAS_Instance

noncomputable section

open scoped BigOperators Classical

namespace HypergraphUnreliability.FPRAS


/-- Lemma 9.3, p. 15: for rational `Λ ∈ [0, R]`, a positive rational `q₀` with
`|q₀ / e^{-Λ} - 1| ≤ ε/64` can be computed in time polynomial in the bit encodings, the numerical bound
`R + 1`, and `log(1/ε)` (the last being bounded by the encoding of `ε`). The dependence on `R` is on its
value, through `⌈R⌉`, not on its bit length. -/
theorem lemma_9_3 :
    ∃ f : ExpInput → Frac,
      (∀ x, x.InDomain → 0 < (f x).den ∧ 0 < (f x).val ∧
        |((((f x).val : ℚ) : ℝ) / Real.exp (-((x.Λ.val : ℚ) : ℝ))) - 1| ≤
          ((x.ε.val : ℚ) : ℝ) / 64) ∧
      PolyComputesIn ExpInput.InDomain ExpInput.encode (fun x => fracCode (f x))
        (fun x => x.encode.length + ⌈((x.R.val : ℚ) : ℝ)⌉₊ + 1) := by sorry

end HypergraphUnreliability.FPRAS
