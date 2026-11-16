-- Prove2me | Theorems.Thm_MatrixQuantumSampler595_Correspondence_Supplement_internal_seed_extraction
-- name    : MatrixQuantumSampler595.Correspondence.Supplement.internal_seed_extraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:00:42.549839+00:00
-- url     : https://prove2.me/theorems/c48eb20f-1eab-4ce4-8a6a-7913b189af26
-- title:
--   Theorem 5.3 — internal-seed extraction
-- statement:
--   Fix real constants $0<\mu\le1$, $A>0$ and $C_M>0$. There are $c,C_d>0$, an integer $n_0\ge1$, and a uniform explicit family depending only on these constants. For every integer $n\ge n_0$, every real $\mu n\le k\le n$ and $2^{-cn}\le\eta\le1/2$, put $h=\log_2(n/\eta)$. The family gives a strong conditional-min-entropy quantum-proof $(k,\eta)$ extractor with
--
--   $$d\le C_dh,\qquad M=\left\lfloor C_Mh\bigl(\log_2(n/h)\bigr)^A\right\rfloor.$$
--
--   The output length is exactly $M$. One finite deterministic evaluator runs in polynomial time for fixed $\mu,A,C_M$. The threshold and $c$ incorporate the sufficiently large $n/h$ conditions in the proof; no extra ratio hypothesis is imposed. This companion records the internal-seed construction at its exact requested output length.
--
--   **Formalization Note** Integer accuracy controls round $16\log_2(1/\eta)$ upward (sampling uses $\varepsilon$); varying entropy controls round $16k$ downward. Security and displayed bounds use the original real parameters. Fixed-rate families need no entropy control. Theorem 5.3 supplies its exact requested output length as an integer control, and Theorem 6.4 supplies $\ell$. The actual machine and its polynomial are part of the uniform explicitness witness.
--
--   Differences from the source:
--   - encoding: binary source, seed and output strings with one-based sample/coordinate labels → Fin-indexed Boolean strings and a uniform Fin(2^d) seed alphabet with zero-based labels; reason: finite relabelling preserves all states, probabilities and maps
--   - encoding: explicit construction with polynomial-time evaluation for the displayed fixed parameters → one finite TM2 machine computes lengths and samples from the specified integer controls for the entire family; reason: step semantics and canonical rounded numerical inputs express uniform polynomial time without real oracles or advice
--   - encoding: O and Omega with only the printed fixed-parameter dependencies → positive real resource constants and positive eventual integer thresholds quantified before varying instances; reason: uniform quantified meaning of the asymptotic resource bounds supported by the construction proofs
-- source:
--   Kuan Cheng, Ruiyang Wu, STOC 2027 submission #595 (October 2026), canonical held PDF (SHA-256 35e315808fa8dd8704a13971c8ca60bc3f785907b566f8914e4bb929c38b26af), Theorem 5.3, printed/PDF p.21; pp.22–25

import Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_ConditionalExtractor
import Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_UniformConstruction

namespace MatrixQuantumSampler595.Correspondence.Supplement

/-- Theorem 5.3, p.21: the requested output length is the exact floor, not a lower bound. -/
theorem internal_seed_extraction
    (mu A CM : ℝ) (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hA : 0 < A) (hCM : 0 < CM) :
    ∃ (c Cd : ℝ) (n0 : ℕ) (E : Controls → FiniteSeededMap),
      0 < c ∧ 0 < Cd ∧ 1 ≤ n0 ∧ IsUniformExplicit E ∧
      ∀ n : ℕ, n0 ≤ n → ∀ (k eta : ℝ), mu * n ≤ k → k ≤ n →
        (2 : ℝ) ^ (-c * n) ≤ eta → eta ≤ 1 / 2 →
        let h := logTwo ((n : ℝ) / eta)
        let M : ℕ := ⌊CM * h * (logTwo ((n : ℝ) / h)) ^ A⌋₊
        let F := E ⟨n, 0, accuracyControl eta, M⟩
        F.sourceLength = n ∧ F.outputLength = M ∧
        ∃ d : ℕ, F.samples = 2 ^ d ∧ (d : ℝ) ≤ Cd * h ∧
          IsStrongConditionalExtractor F.apply k eta := by sorry

end MatrixQuantumSampler595.Correspondence.Supplement
