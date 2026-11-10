-- Prove2me | Theorems.Thm_HarmonicCalib_Principal_lemma_3_1
-- name    : HarmonicCalib.Principal.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:06:39.259104+00:00
-- url     : https://prove2.me/theorems/bd84ff78-17d7-4e6f-a18e-02df7042cbb9
-- title:
--   Lemma 3.1 — comparison of harmonic normalizations $\tfrac13\Gamma(K_T) \le h_T\Gamma(\widehat K_T) \le 3\Gamma(K_T)$
-- statement:
--   For nonempty compact convex sets $A, B \subseteq \mathbb R^d$ with $B = -B$, and every $T \ge 1$,
--   $$\tfrac{1}{3}\,\Gamma^{(T)}_{A,B}(K_T) \le h_T\, \Gamma^{(T)}_{A,B}(\widehat K_T) \le 3\, \Gamma^{(T)}_{A,B}(K_T).$$
--
--   Differences from the source:
--   - encoding: B = −B → -B = B (pointwise negation); reason: the same condition
--   - encoding: ℝ^d with the standard inner product → EuclideanSpace ℝ (Fin d) with ⟪·,·⟫_ℝ; reason: the same space; coordinates are x i for i : Fin d
--   - encoding: Γ^{(T)} and γ as real suprema → Gamma and gammaCoef valued in EReal (iSup); reason: an EReal supremum is never a junk value; on nonempty compact sets Γ is finite and the EReal comparison is the real one
-- source:
--   Fishelson and Mohri (2026), High-Dimensional Online Calibration from Harmonic Weights, arXiv:2610.07740 (version dated October 29, 2026; PDF SHA256 62ac31a3…), Lemma 3.1, p. 11 (proved in Appendix D.1, pp. 53–54)

import Mathlib
import Definitions.Def_HarmonicCalib_Principal_Hilbert
import Definitions.Def_HarmonicCalib_Principal_Discrepancy

open scoped Pointwise

namespace HarmonicCalib.Principal

/-- Lemma 3.1 (comparison of harmonic normalizations, p. 11): for nonempty compact convex
`A, B ⊆ ℝ^d` with `B = -B` and every `T ≥ 1`,
`(1/3) Γ^{(T)}_{A,B}(K_T) ≤ h_T Γ^{(T)}_{A,B}(K̂_T) ≤ 3 Γ^{(T)}_{A,B}(K_T)`. -/
theorem lemma_3_1 :
    ∀ (d : ℕ) (A B : Set (EuclideanSpace ℝ (Fin d))),
      A.Nonempty → IsCompact A → Convex ℝ A →
      B.Nonempty → IsCompact B → Convex ℝ B → -B = B →
      ∀ T : ℕ, 1 ≤ T →
        ((1 / 3 : ℝ) : EReal) * Gamma A B T (hilbertK T) ≤
            ((harm T : ℝ) : EReal) * Gamma A B T (hilbertKhat T) ∧
        ((harm T : ℝ) : EReal) * Gamma A B T (hilbertKhat T) ≤
            ((3 : ℝ) : EReal) * Gamma A B T (hilbertK T) := by sorry

end HarmonicCalib.Principal
