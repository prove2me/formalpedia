-- Prove2me | Theorems.Thm_KoanaKPaths_Main_sign_determinant_fourth_moment
-- name    : KoanaKPaths.Main.sign_determinant_fourth_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T00:06:53.417849+00:00
-- url     : https://prove2.me/theorems/60f5a9e3-011b-4b2f-b749-bdbf55274c89
-- title:
--   Random sign determinant fourth moment
-- statement:
--   Let $\tau:[k]\to[n]$ be injective, and assign independent uniform sign vectors $\sigma_j\in\{-1,1\}^k$ to the $n$ labels. Write $D_\tau=\det[\sigma_{\tau_1}\ \cdots\ \sigma_{\tau_k}]$. For $k\ge1$,
--
--   $$\mathbb E_\sigma D_\tau^4\le(k!)^2k^3.$$
--
--   This determinant moment bound supplies the relative second-moment estimate for the tensor norm in Lemma 4. Extra unused label vectors have no effect on the expectation.
-- source:
--   Tomohiro Koana, Approximate Counting of k-Paths in O*(2^k) Time, STOC 2027 submission #953, printed p. 6 / PDF p. 7, proof of Lemma 4, determinant-moment formulas attributed to Nyquist, Rice and Riordan (1954). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/953.pdf

import Definitions.Def_KoanaKPaths_Main_Estimator

theorem KoanaKPaths.Main.sign_determinant_fourth_moment (n k : ℕ) (hk : 1 ≤ k)
    (τ : Fin k → Fin n) (hτ : Function.Injective τ) :
    KoanaKPaths.Main.uniformMean (fun σ : KoanaKPaths.Main.Labels n k =>
      (KoanaKPaths.Main.detD σ τ : ℝ)^4) ≤
      (Nat.factorial k : ℝ)^2 * (k : ℝ)^3 := by sorry
