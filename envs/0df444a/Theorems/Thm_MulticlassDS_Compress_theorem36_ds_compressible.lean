-- Prove2me | Theorems.Thm_MulticlassDS_Compress_theorem36_ds_compressible
-- name    : MulticlassDS.Compress.theorem36_ds_compressible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:04:11.314127+00:00
-- url     : https://prove2.me/theorems/2e95e7dc-8033-439a-b9ea-cea8c036eb96
-- title:
--   Theorem 36, p. 22 — finite DS dimension gives an n → r sample compression scheme with r ≤ ((d+t+1)/(t+1)(d+t) + 10³ d_N log(C(d+t+1, t+1) log 2n)) log 2n
-- statement:
--   **DS classes are compressible.** Let $\mathcal H\subseteq\mathcal Y^{\mathcal X}$ be a class with DS dimension $d_{DS}<\infty$ and Natarajan dimension $d_N$. For all integers $n,t>0$ there is an $n\to r$ sample compression scheme for $\mathcal H$ (with $r\le n$) such that
--   $$r\ \le\ \left(\frac{d_{DS}+t+1}{t+1}\,(d_{DS}+t) + 10^3\,d_N\log\!\left(\binom{d_{DS}+t+1}{t+1}\log(2n)\right)\right)\log(2n),$$
--   with all logarithms in base $2$.
--
--   For constant $d_{DS}$ and $t = \lceil d_{DS}^{1/2}\rceil$ this is $r = \tilde O(d_{DS}^{3/2}\log n)$: every class of finite DS dimension, over an arbitrary (possibly infinite) label set, has sample compression schemes of size polylogarithmic in the sample size. By the "compression implies generalization" principle this yields the paper's main theorem, that finite DS dimension implies PAC learnability.
--
--   **Formalization Note** The dimensions are given as natural numbers through `dsDim H = dDS` and `natarajanDim H = dN` (so $d_{DS}<\infty$; $d_N\le d_{DS}$ is then automatically finite). The condition $r\le n$ of Definition 35 is part of the conclusion; it does not weaken the statement, because for any $r\ge n$ one may keep the whole sample. The reconstruction function $\rho$ is chosen before the sample, as in Definition 35. Logarithms are `Real.logb 2`; for $n\ge1$, $\log(2n)\ge1$.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 22, Theorem 36 (with Definition 35, p. 22)

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_Compression

namespace MulticlassDS.Compress

theorem theorem36_ds_compressible {X Y : Type*} (H : Set (X → Y)) (dDS dN : ℕ)
    (hDS : dsDim H = dDS) (hN : natarajanDim H = dN) (n t : ℕ) (hn : 0 < n) (ht : 0 < t) :
    ∃ r : ℕ, r ≤ n ∧
      (r : ℝ) ≤ (((dDS : ℝ) + t + 1) / (t + 1) * (dDS + t) +
          10 ^ 3 * dN * Real.logb 2 ((Nat.choose (dDS + t + 1) (t + 1) : ℝ) *
            Real.logb 2 (2 * (n : ℝ)))) * Real.logb 2 (2 * (n : ℝ)) ∧
      ∃ ρ : (Fin r → X × Y) → X → Y, IsCompressionScheme H n r ρ := by sorry

end MulticlassDS.Compress
