-- Prove2me | Theorems.Thm_MixScale_lemma_D_2
-- name    : MixScale.lemma_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:12:01.744183+00:00
-- url     : https://prove2.me/theorems/253495e3-cbcb-4a29-8e1f-66e62aa1a2dd
-- title:
--   Lemma D.2, p.27 — stable measurements
-- statement:
--   Let $\|z\|\le1/(100d^{3/2})$ and let $P,Q$ be the designs (46). Then $\sigma_{\min}(P)\ge1/2$ and $\sigma_{\min}(Q)\ge1/(2\sqrt d)$. If matched projected centers and scales have errors at most $e_b,e_v$ and $\hat\mu,\hat\Sigma$ are the least-squares reconstructions, then
--
--   $$\|\hat\mu-\mu\|_2\le2de_b,\qquad\|\hat\Sigma-\Sigma\|_F\le2d^{3/2}e_v.$$
--
--   This is the step that reassembles a center and a scale matrix from scalar measurements without any loss depending on the separation.
--
--   Differences from the source:
--   - generalization: On G → under clause 3 of G only: ‖z‖ ≤ 1/(100 d^{3/2}); reason: G implies clause 3, and the proof uses no other clause
--   - encoding: σ_min(A) ≥ s → ‖Ax‖₂ ≥ s‖x‖₂ for all x; reason: the definition of the smallest singular value of a full-column-rank matrix
--   - encoding: the least-squares reconstructions → any minimizers of ‖Px − b̂‖₂ and ‖Qy − v̂‖₂, with Σ̂ = svec⁻¹(ŷ); reason: the designs have full column rank, so the minimizer is P†b̂ and Q†v̂
--   - generalization: μ_j, Σ_j the center and scale matrix of a component under (2) → any μ ∈ ℝ^d and any symmetric matrix Σ; reason: the proof uses only that Σ is symmetric (svec is an isometry on symmetric matrices); the paper's Σ_j are symmetric with κ⁻¹I ⪯ Σ_j ⪯ κI, a special case
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Lemma D.2, p.27 (PDF p.29); (46), p.27

import Mathlib
import Definitions.Def_DDROCS_frobNorm
import Definitions.Def_MixScale_Directions

namespace MixScale

/-- **Lemma D.2** (Stable measurements).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Lemma D.2, p.27 (PDF p.29), with (46), p.27.

**Formalization Note.** The hypothesis is clause 3 of `G`, `‖z‖ ≤ 1/(100 d^{3/2})`, which is all the
proof uses. `σ_min(A) ≥ s` is `‖Ax‖₂ ≥ s‖x‖₂` for all `x`. Least-squares solutions are the
minimizers of `‖Px − b̂‖₂`, `‖Qy − v̂‖₂` (`P†b̂` and `Q†v̂`, since both designs have full column rank
here), and `Σ̂ = svec⁻¹(ŷ)`. -/
theorem lemma_D_2 {d : ℕ} (hd : 0 < d) (z : Vec d)
    (hz : ‖z‖ ≤ 1 / (100 * (d : ℝ) ^ (3 / 2 : ℝ))) :
    (∀ x : Fin d → ℝ, (1 / 2) * l2 x ≤ l2 ((designP z).mulVec x)) ∧
    (∀ y : StableIdx d → ℝ, (2 * Real.sqrt d)⁻¹ * l2 y ≤ l2 ((designQ z).mulVec y)) ∧
    ∀ (μ μhat : Vec d) (Sig : Matrix (Fin d) (Fin d) ℝ) (yhat bhat vhat : StableIdx d → ℝ)
      (eb ev : ℝ), Sig.IsSymm →
      (∀ p, |bhat p - inner ℝ (stableDir z p) μ| ≤ eb) →
      (∀ p, |vhat p - quadForm Sig (stableDir z p)| ≤ ev) →
      (∀ x : Fin d → ℝ, l2 ((designP z).mulVec (fun a => μhat a) - bhat) ≤
        l2 ((designP z).mulVec x - bhat)) →
      (∀ y : StableIdx d → ℝ, l2 ((designQ z).mulVec yhat - vhat) ≤
        l2 ((designQ z).mulVec y - vhat)) →
      ‖μhat - μ‖ ≤ 2 * (d : ℝ) * eb ∧
      DDROCS.frobNorm (svecInv yhat - Sig) ≤ 2 * (d : ℝ) ^ (3 / 2 : ℝ) * ev := by sorry

end MixScale
