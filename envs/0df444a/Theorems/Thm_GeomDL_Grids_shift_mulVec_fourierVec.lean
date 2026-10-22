-- Prove2me | Theorems.Thm_GeomDL_Grids_shift_mulVec_fourierVec
-- name    : GeomDL.Grids.shift_mulVec_fourierVec
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:19.504979+00:00
-- url     : https://prove2.me/theorems/ab845782-ad81-4bca-94c4-dd969b390d90
-- title:
--   §4.2, p. 38 — the Fourier basis vectors are eigenvectors of S, Sφ_k = e^{−2πik/n} φ_k, with root-of-unity eigenvalues
-- statement:
--   Let $n \ge 1$, let $S$ be the right shift on $\mathbb C^{\mathbb Z_n}$, and let $\varphi_k(u) = n^{-1/2} e^{2\pi i k u/n}$ be the discrete Fourier basis. For every $k \in \{0, \dots, n-1\}$, $\varphi_k$ is an eigenvector of $S$ with eigenvalue $\lambda_k = e^{-2\pi i k/n}$, and this eigenvalue is an $n$-th root of unity:
--   $$S\varphi_k = e^{-2\pi i k / n}\,\varphi_k, \qquad \big(e^{-2\pi i k/n}\big)^n = 1 .$$
--
--   The book names the eigenvectors and says in a side-note that the eigenvalues are complex roots of unity; the eigenvalue itself is left implicit on the page and is computed from $(S x)_u = x_{u-1}$.
--
--   **Formalization Note** The index $k$ ranges over `ZMod n` and enters the exponent through its representative `k.val` $\in \{0, \dots, n-1\}$. The root-of-unity conjunct comes from the side-note on the same page ("the eigenvalues are complex (roots of unity)").
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.2, p. 38, "the eigenvectors happen to be the discrete Fourier basis" and side-note p. 38, "the eigenvalues are complex (roots of unity)"

import Mathlib
import Definitions.Def_GeomDL_Grids_Defs

open Matrix

namespace GeomDL.Grids
/-- Bronstein et al. §4.2, p. 38 and side-note p. 38: the discrete Fourier basis vectors are
eigenvectors of the shift, `Sφ_k = λ_k φ_k` with `λ_k = e^{-2πik/n}`, and each eigenvalue is a
root of unity, `λ_k^n = 1`. -/
theorem shift_mulVec_fourierVec {n : ℕ} [NeZero n] (k : ZMod n) :
    shift ℂ n *ᵥ fourierVec n k =
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ))) • fourierVec n k ∧
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ))) ^ n = 1 := by sorry
end GeomDL.Grids
