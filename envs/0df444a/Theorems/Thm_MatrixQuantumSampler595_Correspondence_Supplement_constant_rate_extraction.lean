-- Prove2me | Theorems.Thm_MatrixQuantumSampler595_Correspondence_Supplement_constant_rate_extraction
-- name    : MatrixQuantumSampler595.Correspondence.Supplement.constant_rate_extraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:58:26.936489+00:00
-- url     : https://prove2.me/theorems/00811aa9-34c7-4313-8a54-395b3672ee28
-- title:
--   Theorem 1.8 — constant-rate extraction
-- statement:
--   Fix a real rate $0<\mu<1$. There are constants $c,A,b>0$, an integer $n_0\ge1$, and a uniform explicit family, all depending only on $\mu$, such that for every integer $n\ge n_0$, every real $\mu n\le k\le n$, and every $0<\eta\le1/2$ with $h=\log_2(n/\eta)\le cn$, a strong conditional-min-entropy quantum-proof $(k,\eta)$ extractor has
--
--   $$d\le Ah,\qquad m\ge bn.$$
--
--   The evaluator is one finite deterministic machine with a polynomial running-time bound for this fixed rate. All constants, the machine and the eventual threshold precede the lengths, entropy, error and cq source. This companion asserts linear output and logarithmic seed length throughout the exponential-error regime at every fixed positive entropy rate.
--
--   **Formalization Note** Integer accuracy controls round $16\log_2(1/\eta)$ upward (sampling uses $\varepsilon$); varying entropy controls round $16k$ downward. Security and displayed bounds use the original real parameters. Fixed-rate families need no entropy control. Theorem 5.3 supplies its exact requested output length as an integer control, and Theorem 6.4 supplies $\ell$. The actual machine and its polynomial are part of the uniform explicitness witness.
--
--   Differences from the source:
--   - encoding: binary source, seed and output strings with one-based sample/coordinate labels → Fin-indexed Boolean strings and a uniform Fin(2^d) seed alphabet with zero-based labels; reason: finite relabelling preserves all states, probabilities and maps
--   - encoding: explicit construction with polynomial-time evaluation for the displayed fixed parameters → one finite TM2 machine computes lengths and samples from the specified integer controls for the entire family; reason: step semantics and canonical rounded numerical inputs express uniform polynomial time without real oracles or advice
--   - encoding: O and Omega with only the printed fixed-parameter dependencies → positive real resource constants and positive eventual integer thresholds quantified before varying instances; reason: uniform quantified meaning of the asymptotic resource bounds supported by the construction proofs
-- source:
--   Kuan Cheng, Ruiyang Wu, STOC 2027 submission #595 (October 2026), canonical held PDF (SHA-256 35e315808fa8dd8704a13971c8ca60bc3f785907b566f8914e4bb929c38b26af), Theorem 1.8, printed/PDF p.6–7; pp.20,25–26

import Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_ConditionalExtractor
import Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_UniformConstruction

namespace MatrixQuantumSampler595.Correspondence.Supplement

/-- Theorem 1.8, pp.6–7: one eventual threshold and constants depending only on mu. -/
theorem constant_rate_extraction (mu : ℝ) (hmu : 0 < mu) (hmu1 : mu < 1) :
    ∃ (c A b : ℝ) (n0 : ℕ) (E : Controls → FiniteSeededMap),
      0 < c ∧ 0 < A ∧ 0 < b ∧ 1 ≤ n0 ∧ IsUniformExplicit E ∧
      ∀ n : ℕ, n0 ≤ n → ∀ (k eta : ℝ), mu * n ≤ k → k ≤ n →
        0 < eta → eta ≤ 1 / 2 → logTwo ((n : ℝ) / eta) ≤ c * n →
        let F := E ⟨n, 0, accuracyControl eta, 0⟩
        F.sourceLength = n ∧ ∃ d : ℕ, F.samples = 2 ^ d ∧
          (d : ℝ) ≤ A * logTwo ((n : ℝ) / eta) ∧
          b * n ≤ F.outputLength ∧ IsStrongConditionalExtractor F.apply k eta := by sorry

end MatrixQuantumSampler595.Correspondence.Supplement
