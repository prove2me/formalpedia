-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_lemma_4_1
-- name    : OptimalTraceDistance.Estimation.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:44:43.822271+00:00
-- url     : https://prove2.me/theorems/bd093cb2-11b6-407b-83a7-b332551bcdcb
-- title:
--   Lemma 4.1 — Fourier coefficients and variance
-- statement:
--   Let $\tau$ be a density on $\mathbb C^m$, $1\le n$, $0\le D\le n$, and let $h_k$ be symmetric Hermitian kernels for $1\le k\le D$. Set $G=f_0I+\sum_{k=1}^DU_{n,k}(h_k)$ for real $f_0$, and $B_j=\sum_{k=j}^D\binom{k}{j}(h_k)_{\tau\to j}$. For every density, including singular ones,
--   $$\operatorname{Var}_{\tau^{\otimes n}}G\le\sum_{j=1}^D\binom nj^{-1}\|B_j\|_{\tau,j}^2.$$
--   If $\tau$ has full rank, a weighted basis exists, and in every such basis the Fourier degree of $G$ is at most $D$. For $S=\operatorname{supp}\alpha$, $1\le |S|=j\le D$,
--   $$\widehat G_\tau(\alpha)=\binom nj^{-1}\widehat B_{j,\tau}(\alpha_S),$$
--   $$W_j(G)=\binom nj^{-1}\sum_{a_1,\ldots,a_j\ne0}|\widehat B_{j,\tau}(a)|^2\le\binom nj^{-1}\|B_j\|_{\tau,j}^2,\qquad \operatorname{Var}G=\sum_{j=1}^DW_j(G).$$
--   Any enumeration of $S$ gives the same formula, by kernel symmetry. The empty degree range $D=0$ is included.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
--   - encoding: Choose a weighted orthonormal basis when τ has full rank → Basis existence plus identities for every such basis; support restriction uses any enumerating injection; reason: Every basis with identity first gives these formulas, and symmetry removes the ordering choice; singular states appear only in the basis-free variance inequality
--   - encoding: Subset-normalized U-statistics of symmetric word kernels → Average over all ordered injective register embeddings; a trailing word coefficient is moved to the first factor by trace cyclicity; reason: Each k-subset occurs k! times in the embedding average, cancelling the identical normalization factor; word traces and symmetric kernels are unchanged
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Lemma 4.1, p. 14.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem lemma_4_1 (m n D : ℕ) (hm : 0 < m) (hn : 1 ≤ n) (hD : D ≤ n)
    (τ : Mat m) (hτ : Density τ) (h : (k : ℕ) → Op m k)
    (hh : ∀ k ∈ Finset.Icc 1 D, (h k).IsHermitian ∧ symmetric (h k)) (f₀ : ℝ) :
  let G := kernelSum n D f₀ h
  let B := effectiveKernel τ D h
  variance τ n G ≤ varianceSum τ n D h ∧
  (τ.det ≠ 0 → Nonempty (FourierBasis m τ) ∧ ∀ FB : FourierBasis m τ,
    (∀ α : Fin n → Fin (m*m), D < supportSize α → fourierCoeff FB G α = 0) ∧
    (∀ j ∈ Finset.Icc 1 D, ∀ α : Fin n → Fin (m*m), supportSize α = j →
      ∀ e : Fin j ↪ Fin n, Set.range e = {i | (α i).val ≠ 0} →
        fourierCoeff FB G α = (Nat.choose n j : ℂ)⁻¹ *
          fourierCoeff FB (B j) (fun i => α (e i))) ∧
    (∀ j ∈ Finset.Icc 1 D,
      fourierWeight FB G j = (Nat.choose n j : ℝ)⁻¹ *
        ∑ a : Fin j → Fin (m*m), if ∀ i, (a i).val ≠ 0 then
          ‖fourierCoeff FB (B j) a‖^2 else 0) ∧
    (∀ j ∈ Finset.Icc 1 D, fourierWeight FB G j ≤
      (Nat.choose n j : ℝ)⁻¹ * weightedNormSq τ j (B j)) ∧
    variance τ n G = ∑ j ∈ Finset.Icc 1 D, fourierWeight FB G j) := by sorry

end OptimalTraceDistance.Estimation
