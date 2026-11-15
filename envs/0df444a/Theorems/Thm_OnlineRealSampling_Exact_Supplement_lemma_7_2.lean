-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_Supplement_lemma_7_2
-- name    : OnlineRealSampling.Exact.Supplement.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:39:11.080788+00:00
-- url     : https://prove2.me/theorems/a9535be2-33d9-4854-ab12-e0bed0e657bf
-- title:
--   Lemma 7.2 — Probability of avoiding high precision
-- statement:
--   Let S be any exact online sampler with access only to CDF oracle answers. Fix any sequence of valid target oracles, and let n,k be arbitrary natural numbers, including zero. Let E_{n,k} be the event that no query in the first n sampling rounds has precision above k, including queries to earlier targets. Under the shared fair-bit source,
--
--   $$\Pr(E_{n,k})\le (1-2^{-k})^n.$$
--
--   The empty prefix gives 1≤1. Exactness is universal over all valid causal target rules and hence over every replacement oracle used to compare executions. This precision bound supports the overall-space lower bound.
--
--   Differences from the source:
--   - encoding: arbitrary online sampling algorithms using CDF oracles → represented-state causal transition programs with a shared sequential fair-bit tape and access to current and previous oracle handles; reason: finite binary representations cover every physical word-RAM state without a space bound; arbitrary deterministic local transitions include all effective local computations, and only query answers enter execution
--   - encoding: a finite sequence of n target oracles → the first n entries of an arbitrary valid sequence indexed from zero; reason: all finite valid sequences extend to such a sequence; execution cannot query future handles and hence ignores the extension
--   - encoding: Pr(E) ≤ (1−2^(−k))^n → the same inequality in extended nonnegative reals; reason: the right side lies in [0,1]; truncated subtraction is the ordinary nonnegative difference; nonterminating low-precision paths are retained in E and have measure zero by exactness
-- source:
--   Draper, Harris and Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, manuscript dated 2026-11-02. Citation basis: preprint; pinned source.pdf SHA-256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; no arXiv identifier/version exists in the artifact, so cite the dated hash-pinned submission with the paper's own result number. PDF 1 is unnumbered; For PDF pages 2–24, printed page = PDF page − 1; PDF 1 is unnumbered. Source artifact: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf. Lemma 7.2, PDF 18 / printed 17; proof PDF 17–19 / printed 16–18.

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Supplement_Observables

open scoped ENNReal

namespace OnlineRealSampling.Exact.Supplement

/-- Lemma 7.2, PDF 18 / printed 17. No restrictions on n or k, including zero. -/
theorem lemma_7_2 {σ : Type} (A : Sampler σ) (hA : IsExact A)
    (O : ℕ → CDFOracle) (hO : ∀ i, (O i).Valid) (n k : ℕ) :
    coinMeasure (lowPrecision A (fixedTargets O) n k) ≤
      (1 - (1 / (2 : ℝ≥0∞) ^ k)) ^ n := by sorry

end OnlineRealSampling.Exact.Supplement
