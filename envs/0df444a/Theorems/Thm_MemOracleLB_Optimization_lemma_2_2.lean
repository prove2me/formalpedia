-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_lemma_2_2
-- name    : MemOracleLB.Optimization.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:00.075462+00:00
-- url     : https://prove2.me/theorems/d394c933-9576-46a0-b86c-0ef3d9163456
-- title:
--   Lemma 2.2 — Gaussian Brascamp–Lieb
-- statement:
--   Let $L_1,\ldots,L_N$ be nonzero subspaces of $E_d$, and let $c_s\ge0$ satisfy $\sum_s c_sP_{L_s}\preceq I_d$. For every probability measure $\mu$ with finite $K(\mu)=D_{\rm KL}(\mu\|\gamma_d)$,
--
--   $$\sum_s c_s D_{\rm KL}((P_{L_s})_\#\mu\|\gamma_{L_s})\le K(\mu).$$
--
--   Here $P_L$ is orthogonal projection into the subspace $L$ and $\gamma_L$ is its standard Gaussian law. The Loewner inequality is an upper bound, not an equality. This is the Gaussian entropy form of Brascamp–Lieb.
--
--   Differences from the source:
--   - encoding: real Euclidean spaces, independent rows and Gaussian relative entropy → EuclideanSpace with Fin indices, product measures and Mathlib klDiv in [0,infinity]; reason: the same spaces, independent laws and divergence values, including infinite entropy
--   - generalization: the ambient large-dimension convention of §2 → every finite dimension and every finite number of subspaces; reason: the same Gaussian Brascamp–Lieb inequality holds in every dimension and includes the source regime
--   - encoding: the matrix inequality on the sum of orthogonal projections → the quadratic-form inequality sum c_s norm(P_Ls x)^2 at most norm(x)^2 for every x; reason: orthogonal projections are self-adjoint and idempotent, so these inequalities are identical
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Lemma 2.2, PDF p. 9 (printed p. 8), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_Probability

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace

namespace MemOracleLB.Optimization

/-- Lemma 2.2, PDF p.9 (printed p.8). The projection sum is at most the identity. -/
theorem lemma_2_2 {d N : ℕ} (L : Fin N → Submodule ℝ (E d))
    (hL : ∀ s, L s ≠ ⊥) (c : Fin N → ℝ) (hc : ∀ s, 0 ≤ c s)
    (hproj : ∀ x : E d, ∑ s, c s * ‖(L s).orthogonalProjectionOnto x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (μ : Measure (E d)) [IsProbabilityMeasure μ] (hK : gaussianEntropy μ ≠ ⊤) :
    ∑ s, ENNReal.ofReal (c s) *
      klDiv (μ.map (L s).orthogonalProjectionOnto) (stdGaussian (L s)) ≤ gaussianEntropy μ := by sorry

end MemOracleLB.Optimization
