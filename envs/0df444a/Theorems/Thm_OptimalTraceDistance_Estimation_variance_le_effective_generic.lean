-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_variance_le_effective_generic
-- name    : OptimalTraceDistance.Estimation.variance_le_effective_generic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T06:32:27.622151+00:00
-- url     : https://prove2.me/theorems/64cd858d-5f7e-4595-bb57-d101a25b579b
-- title:
--   Hoeffding variance bound for U-statistic observables (generic alphabet)
-- statement:
--   This is the variance bound of the quantum Hoeffding decomposition (inequality (37) of Lemma 4.1), stated for an arbitrary finite local alphabet and an arbitrary, possibly singular, density operator.
--
--   Let $\iota$ be a finite set and let $\tau$ be a density operator on $\mathbb C^{\iota}$, i.e. $\tau\succeq0$ and $\operatorname{tr}\tau=1$. Let $1\le n$ and $0\le D\le n$. For $1\le k\le D$ let $h_k$ be a Hermitian kernel on $k$ sites which is symmetric, i.e. $U_\pi h_kU_\pi^{*}=h_k$ for every permutation operator $U_\pi$ of the $k$ sites. For $f_0\in\mathbb R$ consider the U-statistic observable on $n$ sites
--   $$
--   G=f_0I+\sum_{k=1}^{D}U_{n,k}(h_k),
--   $$
--   where $U_{n,k}(h)$ averages the embeddings of $h$ into the $n$ sites over all ordered injections of $k$ positions. With the effective kernels $B_j=\sum_{k=j}^{D}\binom kj (h_k)_{\to j}$ (partial traces against $\tau$ on the last $k-j$ sites), the variance of $G$ in the product state $\tau^{\otimes n}$ satisfies
--   $$
--   \operatorname{Var}_{\tau^{\otimes n}}[G]\;\le\;\sum_{j=1}^{D}\binom nj^{-1}\,\operatorname{tr}\!\big(\tau^{\otimes j}B_j^{*}B_j\big).
--   $$
--
--   This is the analytic input for the variance bounds of Proposition 4.3 and Lemma 4.4, where it is applied with the labelled alphabet $\{0,1\}\times[d]$ and the labelled state.
--
--   **Formalization Note.** The variance is $\operatorname{tr}(\tau^{\otimes n}G^2)-\operatorname{tr}(\tau^{\otimes n}G)^2$ (real parts), and $\operatorname{tr}(\tau^{\otimes j}B^{*}B)$ is the platform's `weightedNormSq`. The effective kernel uses the generic definitions `glueGen`, `contractionGen`, `effectiveKernelGen`.
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875, Lemma 4.1, inequality (37), pp. 13-15 (variance bound, including the singular case via the limit argument)

import Definitions.Def_OptimalTraceDistance_Estimation_Observables
import Definitions.Def_OptimalTraceDistance_Estimation_HoeffdingGen

open scoped BigOperators Matrix ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation
theorem variance_le_effective_generic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : Matrix ι ι ℂ) (hτ : τ.PosSemidef) (htr : τ.trace = 1)
    (n D : ℕ) (hn : 0 < n) (hD : D ≤ n)
    (h : (k : ℕ) → Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (hherm : ∀ k ∈ Finset.Icc 1 D, (h k).IsHermitian)
    (hsym : ∀ k ∈ Finset.Icc 1 D, ∀ π : Equiv.Perm (Fin k),
      permutationOp π * h k * (permutationOp π)ᴴ = h k)
    (f₀ : ℝ) :
    variance τ n ((f₀ : ℂ) • 1 + ∑ k ∈ Finset.Icc 1 D, uStatistic n k (h k)) ≤
      ∑ j ∈ Finset.Icc 1 D, ((Nat.choose n j : ℝ))⁻¹ *
        weightedNormSq τ j (effectiveKernelGen τ D h j) := by sorry

end OptimalTraceDistance.Estimation
