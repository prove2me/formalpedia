-- Prove2me | Theorems.Thm_MaxEntSampling_lemma_3
-- name    : MaxEntSampling.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:59:38.875473+00:00
-- url     : https://prove2.me/theorems/be3d7a27-c7ff-4e3c-b5aa-a7befef1d822
-- title:
--   Lemma 3 — the conjugate of $-\log\det_s$ at $X$, (7) and (8)
-- statement:
--   Let $X\in\mathbb R^{d\times d}$, $X\succeq0$, have rank $r\in[s,d]$ and eigenvalues $\lambda_1\ge\cdots\ge\lambda_d$, and let $s\ge1$. Then
--
--   $$
--   \min_{\Lambda\succ0}\Bigl\{-\log{\det}_s(\Lambda)+\operatorname{tr}(X\Lambda)\Bigr\} = \min_{\beta\in\mathbb R^d_+,\ 0<\beta_1\le\cdots\le\beta_d}\Bigl\{-\sum_{i\in[s]}\log\beta_i+\sum_{i\in[d]}\lambda_i\beta_i\Bigr\} \tag{7}
--   $$
--
--   and
--
--   $$
--   \min_{\beta\in\mathbb R^d_+,\ 0<\beta_1\le\cdots\le\beta_d}\Bigl\{-\sum_{i\in[s]}\log\beta_i+\sum_{i\in[d]}\lambda_i\beta_i\Bigr\} = \Gamma_s(X)+s. \tag{8}
--   $$
--
--   Both minima are attained. This identifies the inner minimization over $\Lambda$ when LD (5) is dualized, which yields PC (9) (Theorem 2).
--
--   **Formalization Note** The statement asserts a real number $m$ that is the least value of both programs and equals $\Gamma_s(X)+s$ in the extended reals ($\Gamma_s(X)$ is finite since $\operatorname{rank}X\ge s$). $\lambda$ is the decreasingly sorted eigenvalue vector.
--
--   Differences from the source:
--   - encoding: rank r ∈ [s,d], eigenvalues λ1 ≥ ··· ≥ λr > λr+1 = ··· = λd = 0, X = Q Diag(λ) Qᵀ → s ≤ X.rank and λ = eigDesc X; reason: rank X ≤ d always holds, and the spectral description and the orthonormal Q are notation for the eigenvalues of X; same instances
--   - reading: the equalities of minima (7) and (8) → a real m that is IsLeast of both sets with (m : EReal) = Γ_s(X) + s; reason: Appendix A.3 constructs optimizers of both programs, so both minima are attained
--   - encoding: β ∈ R^d_+, 0 < β1 ≤ ··· ≤ βd → (∀ i, 0 < β i) ∧ Monotone β; reason: same vectors
--   - encoding: Γ_s(X) + s → EReal sum with Γ_s extended-real valued; reason: Lean convention; Γ_s(X) is finite under the hypotheses
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Lemma 3, eqs. (7)–(8), pp.8–9 (PDF pp.8–9); proof Appendix A.3, pp.43–44

import Mathlib
import Definitions.Def_MaxEntSampling_eigDesc
import Definitions.Def_MaxEntSampling_detBot
import Definitions.Def_MaxEntSampling_GammaS

open Matrix Finset

namespace MaxEntSampling

/-- **Lemma 3: the conjugate of `−log det_s` at `X`, (7) and (8).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Lemma 3, eqs. (7)–(8), pp.8–9 (PDF pp.8–9); proof in Appendix A.3,
pp.43–44: for a d × d matrix X ⪰ 0 with rank r ∈ [s, d] and eigenvalues
λ1 ≥ ··· ≥ λr > λr+1 = ··· = λd = 0,
(i) `min_{Λ≻0} { −log det_s(Λ) + tr(XΛ) } = min_{β∈R^d_+, 0<β1≤···≤βd} { −Σ_{i∈[s]} log(βi) +
Σ_{i∈[d]} λi βi }` (7);
(ii) the right-hand minimum equals `Γs(X) + s` (8).

There is a real number `m` that is the least value of `−log det_s(Λ) + tr(XΛ)` over `Λ ≻ 0`
and also the least value of `−Σ_{i∈[s]} log β_i + Σ_{i∈[d]} λ_i β_i` over `0 < β₁ ≤ ⋯ ≤ β_d`,
and `m = Γ_s(X) + s`.

**Formalization Note.** `λ = eigDesc X`, the decreasingly sorted eigenvalues; the rank hypothesis
`r ∈ [s, d]` is `s ≤ rank X` (`rank X ≤ d` always holds), and the description of the spectrum and
the orthonormal `Q` with `X = Q Diag(λ) Qᵀ` are notation for "λ are the eigenvalues of X". Both
"min" are stated with `IsLeast` (attained, by the optimizers constructed in A.3). `β ∈ ℝ^d_+` with
`0 < β₁ ≤ ⋯ ≤ β_d` is `(∀ i, 0 < β i) ∧ Monotone β`; `[s]` is `i.val < s`. `Γ_s(X)` lies in
`EReal`; it is finite here because `rank X ≥ s`, and (8) is stated as `(m : EReal) = Γ_s(X) + s`. -/
theorem lemma_3 {d : ℕ} (s : ℕ) (hs1 : 1 ≤ s) (X : Matrix (Fin d) (Fin d) ℝ)
    (hX : X.PosSemidef) (hr : s ≤ X.rank) :
    ∃ m : ℝ,
      IsLeast {z : ℝ | ∃ Λ : Matrix (Fin d) (Fin d) ℝ, Λ.PosDef ∧
          z = -Real.log (detBot s Λ) + (X * Λ).trace} m ∧
      IsLeast {z : ℝ | ∃ β : Fin d → ℝ, (∀ i, 0 < β i) ∧ Monotone β ∧
          z = -(∑ i ∈ univ.filter (fun i : Fin d => i.val < s), Real.log (β i)) +
            ∑ i, eigDesc X i * β i} m ∧
      (m : EReal) = GammaS s X + (s : EReal) := by sorry

end MaxEntSampling
