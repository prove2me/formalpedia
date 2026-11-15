-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_Supplement_lemma_7_1
-- name    : OnlineRealSampling.Exact.Supplement.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:38:32.427198+00:00
-- url     : https://prove2.me/theorems/abbd6e0a-d482-4f52-b5bb-9131af6da702
-- title:
--   Lemma 7.1 — Oracle indistinguishability
-- statement:
--   Let F be any distribution on the natural numbers equipped with a valid CDF oracle φ, and let k≥0. There are rational endpoints a,b such that
--
--   $$b-a\ge 2^{-k},$$
--
--   and for every real c with a<c<b there is a valid CDF oracle ψ for a distribution G satisfying G(0)=c and
--
--   $$\psi(x,j)=\phi(x,j)\qquad(x\in\mathbb N,\ 0\le j\le k).$$
--
--   Thus an interval of possible masses at zero remains compatible with every low-precision answer, including answers at indices absent from any particular execution.
--
--   Differences from the source:
--   - encoding: rational oracle answers with unreduced denominator 2^j → integer numerators at the common precision j; reason: equality of these numerators is equivalent to equality of the returned dyadic values; strict error and all natural indices are unchanged
-- source:
--   Draper, Harris and Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, manuscript dated 2026-11-02. Citation basis: preprint; pinned source.pdf SHA-256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; no arXiv identifier/version exists in the artifact, so cite the dated hash-pinned submission with the paper's own result number. PDF 1 is unnumbered; For PDF pages 2–24, printed page = PDF page − 1; PDF 1 is unnumbered. Source artifact: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf. Lemma 7.1, PDF 17 / printed 16; proof PDF 17–19 / printed 16–18.

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Oracle

namespace OnlineRealSampling.Exact.Supplement

/-- Lemma 7.1, PDF 17 / printed 16; proof continues PDF 18 / printed 17.
Agreement is on all indices and all precisions up to k, not just a sampled trace. -/
theorem lemma_7_1 (O : CDFOracle) (hO : O.Valid) (k : ℕ) :
    ∃ a b : ℚ, (1 / (2 : ℚ) ^ k) ≤ b - a ∧
      ∀ c : ℝ, (a : ℝ) < c → c < (b : ℝ) →
        ∃ P : CDFOracle, P.Valid ∧ P.F 0 = c ∧
          ∀ x j : ℕ, j ≤ k → P.φ x j = O.φ x j := by sorry

end OnlineRealSampling.Exact.Supplement
