-- Prove2me | Theorems.Thm_KingmanSubadditive_PositiveMatrices_limsup_le
-- name    : KingmanSubadditive.PositiveMatrices.limsup_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:51.227635+00:00
-- url     : https://prove2.me/theorems/ca3a6f4c-4e49-4c21-992a-34693ff3b7b9
-- title:
--   Proof of Theorem 5, p. 892 — P{lim sup n⁻¹ log [X_n]_ij ≤ λ} = 1
-- statement:
--   Assume the hypotheses of Theorem 5, let $X_n=Y_1\cdots Y_n$, and let $\lambda$ be a real random variable with $n^{-1}\log[X_n]_{11}\to\lambda$ almost surely. Then for every pair of indices $(i,j)$,
--   $$P\Big\{\limsup_{n\to\infty} n^{-1}\log [X_n]_{ij}\ \le\ \lambda\Big\}=1.$$
--   Combined with (2.2.3), this gives almost-sure convergence of $n^{-1}\log[X_n]_{ij}$ to $\lambda$.
--
--   **Formalization Note.** The extended-real lim sup inequality is written as: almost surely, for every $\varepsilon>0$, eventually $n^{-1}\log[X_n]_{ij}\le\lambda+\varepsilon$. No invariance property of $\lambda$ is assumed.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 892, §2.2, proof of Theorem 5

import Mathlib
import Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
open MeasureTheory Filter Topology

namespace KingmanSubadditive.PositiveMatrices

/-- Proof of Theorem 5, p. 892 (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973)), unnumbered: if `λ` is the almost-sure limit of `n⁻¹ log [X_n]₁₁`, then
for every `(i, j)`, `P{lim sup n⁻¹ log [X_n]_ij ≤ λ} = 1` (deduced in the paper from the same
bound for `X_n′ = Y₂ ⋯ Y_{n+1}` and stationarity).

**Formalization Note.** `λ` is any real random variable with `n⁻¹ log [X_n]₁₁ → λ` almost
surely. "lim sup aₙ ≤ λ" in the extended reals is encoded as: for every `ε > 0`, eventually
`aₙ ≤ λ + ε`. No shift-invariance of `λ` is assumed. -/
theorem limsup_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y)
    (lam : Ω → ℝ)
    (hlam : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Real.log (X Y n ω 0 0) / n) atTop (𝓝 (lam ω)))
    (i j : Fin k) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, Real.log (X Y n ω i j) / n ≤ lam ω + ε := by sorry

end KingmanSubadditive.PositiveMatrices
