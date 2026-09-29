-- Prove2me | Theorems.Thm_NaculichRegge_regge_color_extended_basis
-- name    : NaculichRegge.regge_color_extended_basis
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T23:55:14.269574+00:00
-- url     : https://prove2.me/theorems/0c29cee9-1afb-478d-bf67-2e1f25f9edac
-- title:
--   Regge colour factors lie in the $\ell$-loop extended trace basis
-- statement:
--   For every loop order $\ell$ and admissible $(i,k)$ with $i\le\ell$, the $\ell$-loop colour factor $N^{\ell-i}C_{ik}$ is a linear combination (with constant coefficients) of the extended trace basis elements $t^{(\ell)}_1,\dots,t^{(\ell)}_{3\ell+3}$, namely
--   $$N^{\ell-i}C_{ik}=\sum_{\lambda=1}^{3\ell+3}\big(N^{\ell-i}C_{ik}\big)_\lambda\,t^{(\ell)}_\lambda,$$
--   where $(\cdot)_\lambda$ is the $\lambda$-th extended-trace coordinate. In particular only the powers of $N$ allowed by eq. (2.3) occur.
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, pp. 5, 16, eqs. (2.3)–(2.4), (4.24)

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial

namespace NaculichRegge

/-- Naculich, eqs. (2.3)–(2.4), (4.24): for `i ≤ ℓ`, the `ℓ`-loop Regge colour factor
`N^{ℓ−i} C_{ik}` is exactly the combination `∑_{λ=1}^{3ℓ+3} (coordinate λ) · t_λ^{(ℓ)}` of the
extended trace basis. -/
theorem regge_color_extended_basis (ℓ i k : ℕ) (h : IsReggeIndex i k) (hi : i ≤ ℓ) :
    (X : ℂ[X]) ^ (ℓ - i) • reggeColor i k =
      ∑ lam ∈ Finset.Icc 1 (3 * ℓ + 3),
        extCoord ℓ ((X : ℂ[X]) ^ (ℓ - i) • reggeColor i k) lam • extBasisVec ℓ lam := by sorry

end NaculichRegge
