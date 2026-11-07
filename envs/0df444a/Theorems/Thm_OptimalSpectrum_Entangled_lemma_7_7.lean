-- Prove2me | Theorems.Thm_OptimalSpectrum_Entangled_lemma_7_7
-- name    : OptimalSpectrum.Entangled.lemma_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:22:59.147988+00:00
-- url     : https://prove2.me/theorems/1db3f500-de83-4cbf-87d0-80389078b9e4
-- title:
--   Lemma 7.7 — trace derivative formula with bounded coefficients
-- statement:
--   Let $p$ be a real polynomial of degree at most $k$, let $\sigma=\mathrm{diag}(\lambda_1,\dots,\lambda_d)$ with $\lambda_i\in[0,L]$, and let $1\le r\le k$. There are real coefficients $w_{i_1,\dots,i_r}$, symmetric in their indices, with $|w_{i_1,\dots,i_r}|\le\|p^{(r)}\|_{\infty,[0,L]}$, such that for all Hermitian $H_1,\dots,H_r\in\mathbb C^{d\times d}$
--
--   $$D^{(r)}_p(H_1,\dots,H_r)=\frac1{(r-1)!}\sum_{\substack{\pi\in S_r\\\pi(1)=1}}\ \sum_{i_1,\dots,i_r=1}^dw_{i_1,\dots,i_r}\prod_{j=1}^r\big[H_{\pi(j)}\big]_{i_ji_{j+1}},\qquad i_{r+1}=i_1.\tag{50}$$
--
--   The sum runs over all orders of $H_2,\dots,H_r$ with $H_1$ first. This divided-difference representation is the input to the norm bounds of Lemma 7.9.
--
--   Differences from the source:
--   - encoding: 1-based indices, π(1) = 1, i_(r+1) = i_1 → 0-based indices: π 0 = 0 and i (finRotate r j); both sides of (50) compared in ℂ; reason: index conventions; the right side is real
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Lemma 7.7, Eq. (50), p. 25 (PDF p. 27)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_derivOp
import Definitions.Def_OptimalSpectrum_Entangled_supNormDeriv

open scoped Matrix

namespace OptimalSpectrum.Entangled

/-- **Lemma 7.7 (Trace derivative formula).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Lemma 7.7, printed p. 25 (PDF p. 27): "Let p be a real polynomial of degree at most k, and
let σ = diag(λ₁, …, λ_d) with λ_i ∈ [0, L]. For every 1 ⩽ r ⩽ k, there are real coefficients
w_(i₁,…,i_r), symmetric in their indices, satisfying |w_(i₁,…,i_r)| ⩽ ∥p^(r)∥_(∞,[0,L]), such that,
for all Hermitian H₁, …, H_r ∈ C^(d×d), D_p^(r)(H₁, …, H_r) = (1/(r − 1)!) ∑_(π∈S_r, π(1)=1)
∑_(i₁,…,i_r=1)^d w_(i₁,…,i_r) ∏_(j=1)^r [H_(π(j))]_(i_j i_(j+1)), (50) where i_(r+1) = i₁."

**Formalization Note.** Indices are `0`-based: `π(1) = 1` is `π 0 = 0`, and `i_(j+1)` with
`i_(r+1) = i₁` is `i (finRotate r j)`. "Symmetric in their indices" is invariance under every
permutation of the `r` positions. Both sides of (50) are compared in `ℂ` (the right side is real). -/
theorem lemma_7_7 (d k : ℕ) (p : Polynomial ℝ) (hp : p.natDegree ≤ k) (L : ℝ) (lam : Fin d → ℝ)
    (hlam : ∀ i, lam i ∈ Set.Icc 0 L) (r : ℕ) (hr1 : 1 ≤ r) (hrk : r ≤ k) :
    ∃ w : (Fin r → Fin d) → ℝ,
      (∀ (π : Equiv.Perm (Fin r)) (i : Fin r → Fin d), w (i ∘ π) = w i) ∧
      (∀ i, |w i| ≤ supNormDeriv p r L) ∧
      ∀ H : Fin r → Matrix (Fin d) (Fin d) ℂ, (∀ j, (H j).IsHermitian) →
        ((derivOp p (Matrix.diagonal fun i => (lam i : ℂ)) r H : ℝ) : ℂ) =
          (1 / ((r - 1).factorial : ℂ)) *
            ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin r) => π ⟨0, hr1⟩ = ⟨0, hr1⟩),
              ∑ i : Fin r → Fin d, (w i : ℂ) * ∏ j : Fin r, H (π j) (i j) (i (finRotate r j)) := by sorry

end OptimalSpectrum.Entangled
