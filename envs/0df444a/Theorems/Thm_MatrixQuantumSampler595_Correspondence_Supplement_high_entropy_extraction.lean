-- Prove2me | Theorems.Thm_MatrixQuantumSampler595_Correspondence_Supplement_high_entropy_extraction
-- name    : MatrixQuantumSampler595.Correspondence.Supplement.high_entropy_extraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:57:15.357975+00:00
-- url     : https://prove2.me/theorems/4e82329a-21a8-483b-bbe2-89e4abe56ba9
-- title:
--   Theorem 1.7 — high-entropy extraction
-- statement:
--   Fix $\alpha>0$. There are positive constants $C_d,C_m$, depending only on $\alpha$, and a uniform explicit family such that, for every integer $n\ge1$, every real $0\le k\le n$ and $0<\eta\le1/2$, it gives a strong conditional-min-entropy quantum-proof $(k,\eta)$ extractor with source length $n$, seed length $d$, and output length $m$. Writing $a=n-k$ and $\log a=\log_2\max\{2,a\}$,
--
--   $$d\le(1+\alpha)\log a+(2+\alpha)\log_2(1/\eta)+C_d,\qquad m\ge n-C_m(a+\log_2(1/\eta)).$$
--
--   One finite deterministic evaluator runs in time polynomial in $n+\log_2(1/\eta)$ for fixed $\alpha$. Security quantifies over every normalized cq source and arbitrary finite-dimensional quantum side information. Empty output is allowed when the loss bound is nonpositive. This companion retains both the exact leading seed coefficients and the entire output-loss guarantee.
--
--   **Formalization Note** Integer accuracy controls round $16\log_2(1/\eta)$ upward (sampling uses $\varepsilon$); varying entropy controls round $16k$ downward. Security and displayed bounds use the original real parameters. Fixed-rate families need no entropy control. Theorem 5.3 supplies its exact requested output length as an integer control, and Theorem 6.4 supplies $\ell$. The actual machine and its polynomial are part of the uniform explicitness witness.
--
--   Differences from the source:
--   - encoding: binary source, seed and output strings with one-based sample/coordinate labels → Fin-indexed Boolean strings and a uniform Fin(2^d) seed alphabet with zero-based labels; reason: finite relabelling preserves all states, probabilities and maps
--   - encoding: explicit construction with polynomial-time evaluation for the displayed fixed parameters → one finite TM2 machine computes lengths and samples from the specified integer controls for the entire family; reason: step semantics and canonical rounded numerical inputs express uniform polynomial time without real oracles or advice
--   - encoding: O and Omega with only the printed fixed-parameter dependencies → positive real resource constants quantified before all varying instances; reason: uniform quantified meaning of the asymptotic resource bounds supported by the construction proofs
-- source:
--   Kuan Cheng, Ruiyang Wu, STOC 2027 submission #595 (October 2026), canonical held PDF (SHA-256 35e315808fa8dd8704a13971c8ca60bc3f785907b566f8914e4bb929c38b26af), Theorem 1.7, printed/PDF p.6; pp.31–32

import Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_ConditionalExtractor
import Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_UniformConstruction

namespace MatrixQuantumSampler595.Correspondence.Supplement

/-- Theorem 1.7, p.6: exact leading seed coefficients and full output-loss bound. -/
theorem high_entropy_extraction (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ (Cd Cm : ℝ) (E : Controls → FiniteSeededMap),
      0 < Cd ∧ 0 < Cm ∧ IsUniformExplicit E ∧
      ∀ n : ℕ, 1 ≤ n → ∀ (k eta : ℝ), 0 ≤ k → k ≤ n →
        0 < eta → eta ≤ 1 / 2 →
        let a := (n : ℝ) - k
        let F := E ⟨n, entropyControl k, accuracyControl eta, 0⟩
        F.sourceLength = n ∧ ∃ d : ℕ, F.samples = 2 ^ d ∧
          (d : ℝ) ≤ (1 + alpha) * deficiencyLog a +
            (2 + alpha) * logTwo (1 / eta) + Cd ∧
          (n : ℝ) - Cm * (a + logTwo (1 / eta)) ≤ F.outputLength ∧
          IsStrongConditionalExtractor F.apply k eta := by sorry

end MatrixQuantumSampler595.Correspondence.Supplement
