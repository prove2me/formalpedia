-- Prove2me | Theorems.Thm_MatrixQuantumSampler595_Correspondence_Supplement_strong_matrix_sampling
-- name    : MatrixQuantumSampler595.Correspondence.Supplement.strong_matrix_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:56:15.874254+00:00
-- url     : https://prove2.me/theorems/7513f607-ea96-4c65-aff7-135a4114fa2a
-- title:
--   Theorem 1.6 — strong matrix sampling
-- statement:
--   Fix $\alpha>0$. There are positive constants $C_r,C_t$ depending only on $\alpha$ and a uniform explicit family such that, for every pair of integers $m,D\ge1$ and real $0<\delta\le\varepsilon\le1/2$, a strong $D$-dimensional $(\delta,\varepsilon)$ matrix sampler $\mathrm{Samp}:\{0,1\}^r\times[t]\to\{0,1\}^m$ exists with $t\ge1$ and, putting $\Lambda=\log_2(2D/\delta)$,
--
--   $$|r-m|\le C_r\Lambda,\qquad t\le C_t\frac{\Lambda^{1+\alpha}\varepsilon^{-2-\alpha}}{\log_2(\Lambda/\varepsilon)}.$$
--
--   Each sample is computable in time polynomial in $m+\Lambda+\log_2(1/\varepsilon)$, by one finite machine and polynomial chosen for this $\alpha$. The tests are arbitrary position-dependent complex matrices of operator norm at most one, as in the published strong sampler predicate. This companion records the simultaneous randomness and sample guarantees.
--
--   **Formalization Note** Integer accuracy controls round $16\log_2(1/\eta)$ upward (sampling uses $\varepsilon$); varying entropy controls round $16k$ downward. Security and displayed bounds use the original real parameters. Fixed-rate families need no entropy control. Theorem 5.3 supplies its exact requested output length as an integer control, and Theorem 6.4 supplies $\ell$. The actual machine and its polynomial are part of the uniform explicitness witness.
--
--   Differences from the source:
--   - encoding: binary source, seed and output strings with one-based sample/coordinate labels → Fin-indexed Boolean strings and a uniform Fin(t) sample alphabet with zero-based labels; reason: finite relabelling preserves all states, probabilities and maps
--   - encoding: explicit construction with polynomial-time evaluation for the displayed fixed parameters → one finite TM2 machine computes lengths and samples from the specified integer controls for the entire family; reason: step semantics and canonical rounded numerical inputs express uniform polynomial time without real oracles or advice
--   - encoding: O and Omega with only the printed fixed-parameter dependencies → positive real resource constants quantified before all varying instances; reason: uniform quantified meaning of the asymptotic resource bounds supported by the construction proofs
-- source:
--   Kuan Cheng, Ruiyang Wu, STOC 2027 submission #595 (October 2026), canonical held PDF (SHA-256 35e315808fa8dd8704a13971c8ca60bc3f785907b566f8914e4bb929c38b26af), Theorem 1.6, printed/PDF p.5–6; pp.31–32

import Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_ConditionalExtractor
import Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_UniformConstruction

namespace MatrixQuantumSampler595.Correspondence.Supplement

/-- Theorem 1.6, pp.5–6: both resource bounds and uniform polynomial-time per-sample evaluation. -/
theorem strong_matrix_sampling (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ (Cr Ct : ℝ) (E : Controls → FiniteSeededMap),
      0 < Cr ∧ 0 < Ct ∧ IsUniformExplicit E ∧
      ∀ (m D : ℕ), 1 ≤ m → 1 ≤ D → ∀ (delta epsilon : ℝ),
        0 < delta → delta ≤ epsilon → epsilon ≤ 1 / 2 →
        let L := logTwo (2 * (D : ℝ) / delta)
        let F := E ⟨m, upperControl L, accuracyControl epsilon, 0⟩
        F.outputLength = m ∧ 1 ≤ F.samples ∧
        |(F.sourceLength : ℝ) - m| ≤ Cr * L ∧
        (F.samples : ℝ) ≤ Ct * L ^ (1 + alpha) * epsilon ^ (-2 - alpha) /
          logTwo (L / epsilon) ∧
        IsStrongMatrixSampler F.apply D delta epsilon := by sorry

end MatrixQuantumSampler595.Correspondence.Supplement
