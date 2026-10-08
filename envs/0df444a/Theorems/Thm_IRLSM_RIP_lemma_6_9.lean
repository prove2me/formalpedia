-- Prove2me | Theorems.Thm_IRLSM_RIP_lemma_6_9
-- name    : IRLSM.RIP.lemma_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:17.18299+00:00
-- url     : https://prove2.me/theorems/eb5f35ab-2912-47b6-a184-7e495f684c85
-- title:
--   Lemma 6.9 — |⟨S(X), S(Y)⟩| ≤ δ_k‖X‖_F‖Y‖_F for orthogonal X, Y with rank X + rank Y ≤ k
-- statement:
--   Let $\mathcal S : \mathbb R^{n\times p}\to\mathbb R^m$ be a linear map with rank restricted isometry constant $\delta_k > 0$. Let $X, Y$ be $n\times p$ matrices with $\operatorname{rank}X + \operatorname{rank}Y \le k$ and $\langle X, Y\rangle = 0$. Then
--   $$
--   |\langle \mathcal S(X), \mathcal S(Y)\rangle| \le \delta_k\,\|X\|_F\,\|Y\|_F ,
--   $$
--   where $\langle\cdot,\cdot\rangle$ on the left is the Euclidean inner product of $\mathbb R^m$.
--
--   This is Lemma 3.3 of Candès and Plan, recalled in the paper; it controls the cross terms between orthogonal low-rank pieces in the proof of Proposition 6.8.
--
--   **Formalization Note.** Real matrices; $\mathcal S(X)_\ell = \langle A_\ell, X\rangle$; $\delta_k$ is the squared-form constant of Definition 1.1, defined for every $k$.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Lemma 6.9, p. 18

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.RIP

/-- Lemma 6.9 (Lemma 3.3 of Candès–Plan): if `0 < δ_k` and `X`, `Y` are orthogonal
(`⟨X, Y⟩ = 0`) with `rank X + rank Y ≤ k`, then `|⟨S(X), S(Y)⟩| ≤ δ_k ‖X‖_F ‖Y‖_F`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Lemma 6.9, p. 18.

Formalization Notes: real matrices; `S(X)_l = ⟨A_l, X⟩`; `⟨S(X), S(Y)⟩` is the Euclidean dot
product of the two measurement vectors; `δ_k` is `ripConst A k` (squared form of
Definition 1.1, defined for every `k`). -/
theorem lemma_6_9 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (hδ : 0 < IRLSM.Convergence.ripConst A k) (X Y : Matrix (Fin n) (Fin p) ℝ)
    (hrank : X.rank + Y.rank ≤ k) (horth : traceInner X Y = 0) :
    |∑ l, observationOp A X l * observationOp A Y l| ≤
      IRLSM.Convergence.ripConst A k * frobeniusNorm X * frobeniusNorm Y := by sorry

end IRLSM.RIP
