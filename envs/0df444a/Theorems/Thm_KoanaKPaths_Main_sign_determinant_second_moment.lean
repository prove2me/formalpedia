-- Prove2me | Theorems.Thm_KoanaKPaths_Main_sign_determinant_second_moment
-- name    : KoanaKPaths.Main.sign_determinant_second_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T00:06:57.520049+00:00
-- url     : https://prove2.me/theorems/cf15fef2-6313-4a7d-a9df-649821b7fd5e
-- title:
--   Random sign determinant second moment
-- statement:
--   Let $\tau:[k]\to[n]$ be injective, and assign independent uniform sign vectors $\sigma_j\in\{-1,1\}^k$ to the $n$ labels. Write $D_\tau=\det[\sigma_{\tau_1}\ \cdots\ \sigma_{\tau_k}]$. Then
--
--   $$\mathbb E_\sigma D_\tau^2=k!.$$
--
--   This is the random-sign determinant identity used to establish unbiasedness in Lemma 4. The coordinates selected by an injective word form an independent uniform sign matrix. The empty determinant convention includes $k=0$.
-- source:
--   Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, printed p. 6 / PDF p. 7, proof of Lemma 4, determinant-moment formulas attributed to Nyquist, Rice and Riordan (1954). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf

import Definitions.Def_KoanaKPaths_Main_Estimator

theorem KoanaKPaths.Main.sign_determinant_second_moment (n k : ℕ)
    (τ : Fin k → Fin n) (hτ : Function.Injective τ) :
    KoanaKPaths.Main.uniformMean (fun σ : KoanaKPaths.Main.Labels n k =>
      (KoanaKPaths.Main.detD σ τ : ℝ)^2) = (Nat.factorial k : ℝ) := by sorry
