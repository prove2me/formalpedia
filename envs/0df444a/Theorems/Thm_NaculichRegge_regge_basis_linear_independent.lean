-- Prove2me | Theorems.Thm_NaculichRegge_regge_basis_linear_independent
-- name    : NaculichRegge.regge_basis_linear_independent
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:14:27.222021+00:00
-- url     : https://prove2.me/theorems/5bd45316-2abf-410a-bd02-1b8f9860752e
-- title:
--   The Regge colour factors $N^{\ell-i}C_{ik}$ are linearly independent
-- statement:
--   For every loop order $\ell$, the family $\{N^{\ell-i}C_{ik}\}$, indexed by the admissible pairs $(i,k)$ with $i\le\ell$ (one element for $\ell=0$, two for $\ell=1$, $3\ell-2$ for $\ell\ge2$), is linearly independent over $\mathbb C$. Hence the coefficients $B^{(\ell)}_{ik}$ in eq. (4.24) are uniquely determined by the amplitude.
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, pp. 10–11, 16; Sec. 4, eqs. (4.23)–(4.25)

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial

namespace NaculichRegge

/-- Naculich, Sec. 4 (eq. (4.24)): for every loop order `ℓ`, the Regge colour factors
`N^{ℓ−i} C_{ik}`, `(i, k)` ranging over the admissible pairs with `i ≤ ℓ`, are linearly
independent over `ℂ`. -/
theorem regge_basis_linear_independent (ℓ : ℕ) :
    LinearIndependent ℂ
      (fun p : reggeIndex ℓ => ((X : ℂ[X]) ^ (ℓ - p.1.1) • reggeColor p.1.1 p.1.2 : ColorVec)) := by sorry

end NaculichRegge
