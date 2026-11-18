-- Prove2me | Theorems.Thm_KoanaKPaths_Main_fixed_matrix_sketching_moments
-- name    : KoanaKPaths.Main.fixed_matrix_sketching_moments
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T23:59:23.323561+00:00
-- url     : https://prove2.me/theorems/88b28034-0f2b-47a9-a4e7-f28a14fa526f
-- title:
--   Fixed-matrix sign sketch moments, including shared columns
-- statement:
--   Let $X$ be a fixed real $d\times t$ matrix, and let $R$ be an $\ell\times d$ matrix with mutually independent uniform signs as entries. With $\|X\|_F^2=\sum_{u,b}X_{u,b}^2$, averaging over all sign matrices gives
--
--   $$
--   \mathbb E_R\|RX\|_F^2=\ell\|X\|_F^2,\qquad
--   \mathbb E_R\|RX\|_F^4\le(\ell^2+2\ell)\|X\|_F^4.
--   $$
--
--   The same sign matrix acts on every column. These finite moment bounds are the deterministic-matrix part of Lemma 5, and supply the conditional estimate when the input matrix is random and independent of the signs. The formula also includes zero-dimensional matrices, for which the corresponding sums vanish.
-- source:
--   Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953 (October 2026), printed p. 7 / PDF p. 8, Lemma 5, proof for fixed X. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf

import Definitions.Def_KoanaKPaths_Main_Estimator

theorem KoanaKPaths.Main.fixed_matrix_sketching_moments (ℓ d t : ℕ) (X : Fin d → Fin t → ℝ) :
    KoanaKPaths.Main.uniformMean (fun R : Fin ℓ → Fin d → Bool =>
      KoanaKPaths.Main.realFrobSq (KoanaKPaths.Main.signMul R X)) =
        (ℓ : ℝ) * KoanaKPaths.Main.realFrobSq X ∧
      KoanaKPaths.Main.uniformMean (fun R : Fin ℓ → Fin d → Bool =>
        KoanaKPaths.Main.realFrobSq (KoanaKPaths.Main.signMul R X) ^ 2) ≤
        ((ℓ : ℝ)^2 + 2*ℓ) * KoanaKPaths.Main.realFrobSq X ^ 2 := by sorry
