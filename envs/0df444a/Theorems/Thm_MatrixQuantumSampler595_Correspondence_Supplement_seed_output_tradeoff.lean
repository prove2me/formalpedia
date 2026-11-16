-- Prove2me | Theorems.Thm_MatrixQuantumSampler595_Correspondence_Supplement_seed_output_tradeoff
-- name    : MatrixQuantumSampler595.Correspondence.Supplement.seed_output_tradeoff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:01:48.511552+00:00
-- url     : https://prove2.me/theorems/43906a9e-ffff-43d1-ac8b-af3b8a049e3c
-- title:
--   Theorem 6.4 — seed length versus output loss
-- statement:
--   There are an absolute constant $C>0$ and one uniform explicit family such that, for every integer $N\ge1$, every real $0\le k\le N$, every $0<\eta<1/4$ and every integer $\ell\ge1$, there is a strong conditional-min-entropy quantum-proof $(k,\eta)$ extractor with source length $N$, seed length $d$ and output length $m$. Write $a=N-k$ and use the deficiency convention $\log a=\log_2\max\{2,a\}$. Then
--
--   $$d\le2\log_2(1/\eta)+\log_2\ell+\frac a\ell+5,$$
--
--   $$m\ge N-C\left(a+\log_2(1/\eta)+\ell\left[\log a+\log_2(1/\eta)+\log_2\ell\right]\right).$$
--
--   Here $\log_2\ell$ is the actual logarithm, equal to zero at $\ell=1$. One finite deterministic evaluator runs in time polynomial in $N+\log_2(1/\eta)+\ell$. The loss constant and runtime polynomial are uniform in all parameters. Both conclusions include the empty-output branch and there is no upper bound on $\ell$. This companion records the full seed/output tradeoff.
--
--   **Formalization Note** Integer accuracy controls round $16\log_2(1/\eta)$ upward (sampling uses $\varepsilon$); varying entropy controls round $16k$ downward. Security and displayed bounds use the original real parameters. Fixed-rate families need no entropy control. Theorem 5.3 supplies its exact requested output length as an integer control, and Theorem 6.4 supplies $\ell$. The actual machine and its polynomial are part of the uniform explicitness witness.
--
--   Differences from the source:
--   - encoding: binary source, seed and output strings with one-based sample/coordinate labels → Fin-indexed Boolean strings and a uniform Fin(2^d) seed alphabet with zero-based labels; reason: finite relabelling preserves all states, probabilities and maps
--   - encoding: explicit construction with polynomial-time evaluation for the displayed fixed parameters → one finite TM2 machine computes lengths and samples from the specified integer controls for the entire family; reason: step semantics and canonical rounded numerical inputs express uniform polynomial time without real oracles or advice
--   - encoding: O and Omega with only the printed fixed-parameter dependencies → positive real resource constants quantified before all varying instances; reason: uniform quantified meaning of the asymptotic resource bounds supported by the construction proofs
-- source:
--   Kuan Cheng, Ruiyang Wu, STOC 2027 submission #595 (October 2026), canonical held PDF (SHA-256 35e315808fa8dd8704a13971c8ca60bc3f785907b566f8914e4bb929c38b26af), Theorem 6.4, printed/PDF p.29; pp.28–31

import Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_ConditionalExtractor
import Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_UniformConstruction

namespace MatrixQuantumSampler595.Correspondence.Supplement

/-- Theorem 6.4, p.29: the loss constant is absolute; exact seed bound (6.3), including +5. -/
theorem seed_output_tradeoff :
    ∃ (C : ℝ) (E : Controls → FiniteSeededMap), 0 < C ∧ IsUniformExplicit E ∧
      ∀ N : ℕ, 1 ≤ N → ∀ (k eta : ℝ), 0 ≤ k → k ≤ N →
        0 < eta → eta < 1 / 4 → ∀ ell : ℕ, 1 ≤ ell →
        let a := (N : ℝ) - k
        let F := E ⟨N, entropyControl k, accuracyControl eta, ell⟩
        F.sourceLength = N ∧ ∃ d : ℕ, F.samples = 2 ^ d ∧
          (d : ℝ) ≤ 2 * logTwo (1 / eta) + logTwo ell + a / ell + 5 ∧
          (N : ℝ) - C * (a + logTwo (1 / eta) +
            ell * (deficiencyLog a + logTwo (1 / eta) + logTwo ell)) ≤ F.outputLength ∧
          IsStrongConditionalExtractor F.apply k eta := by sorry

end MatrixQuantumSampler595.Correspondence.Supplement
