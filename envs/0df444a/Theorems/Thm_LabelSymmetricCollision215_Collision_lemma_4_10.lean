-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_lemma_4_10
-- name    : LabelSymmetricCollision215.Collision.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:58:51.666491+00:00
-- url     : https://prove2.me/theorems/75e450cb-76c4-4a57-9f00-cc1363f554b8
-- title:
--   Lemma 4.10 — Arrangement Spectral Gap
-- statement:
--   Assume $s\ge1$ and $N\ge2s$. The least eigenvalue of arrangement adjacency on injective tuples is $-s$, and its eigenspace, as a label-permutation representation, is
--   $$\bigoplus_{\mu\vdash s}|\operatorname{SYT}(\mu)|S^{(N-s,\mu)}.$$
--   The next distinct eigenvalue is exactly $N-(3s-2)$, with gap $N-2s+2$. Moreover $-s$ is the unique negative eigenvalue if and only if $N\ge3s-2$. The statement gives existence of both eigenvalues and the lower bounds characterizing least and next distinct eigenvalues. This includes every clause of the spectral result, restated as Lemma 6.1.
--
--   Differences from the source:
--   - encoding: complex Specht modules and standard-tableau multiplicities → published Young left ideals and increasing bijective fillings, transported to cyclic range labels; reason: these are concrete realizations of the same representations and multiplicity sets; height caps exclude no partition of the specified size
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Lemma 4.10, PDF 26 / printed 24

import Definitions.Def_LabelSymmetricCollision215_Collision_Specht

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Lemma 4.10, PDF 26 / printed 24. -/
theorem lemma_4_10 (N s : ℕ) [NeZero N] (hs : 1 ≤ s) (hN : 2*s ≤ N) :
    Eigen N s (-(s : ℝ)) ∧
    (∀ a : ℝ, Eigen N s a → -(s : ℝ) ≤ a) ∧
    EigenDecomposition hN (-(s : ℝ)) ∧
    Eigen N s ((N : ℝ) - (3*(s : ℝ)-2)) ∧
    (∀ a : ℝ, Eigen N s a → -(s : ℝ) < a → (N : ℝ)-(3*(s : ℝ)-2) ≤ a) ∧
    ((N : ℝ)-(3*(s : ℝ)-2)) - (-(s : ℝ)) = (N : ℝ)-2*s+2 ∧
    ((∀ a : ℝ, Eigen N s a → a < 0 → a = -(s : ℝ)) ↔ 3*s-2 ≤ N) := by sorry

end LabelSymmetricCollision215.Collision
