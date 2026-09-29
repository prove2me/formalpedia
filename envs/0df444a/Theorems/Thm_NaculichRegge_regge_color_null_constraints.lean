-- Prove2me | Theorems.Thm_NaculichRegge_regge_color_null_constraints
-- name    : NaculichRegge.regge_color_null_constraints
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:05:14.872849+00:00
-- url     : https://prove2.me/theorems/2473070b-2da0-4dd9-8f9e-3690f21014bc
-- title:
--   Regge colour factors obey the group-theory constraints and have no $t_2$ component
-- statement:
--   For every $\ell\ge2$ and admissible $(i,k)$ with $i\le\ell$, the coordinate vector $(N^{\ell-i}C_{ik})_\lambda$ in the extended trace basis is orthogonal to each of the four $\ell$-loop null vectors $r^{(\ell)}$ of eqs. (2.10), (2.12) (extended to all $\ell$ by prepending zeros, as stated above eqs. (2.14)–(2.15)):
--   $$\sum_{\lambda=1}^{3\ell+3} r^{(\ell)}_\lambda\,(N^{\ell-i}C_{ik})_\lambda=0,$$
--   and its $t^{(\ell)}_2$ component (the leading-colour $N^\ell c[2]$ coefficient, which is suppressed in the Regge limit) vanishes.
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, pp. 5–7, 10–11, 14; eqs. (2.5), (2.10), (2.12), (2.14)–(2.15), footnote 6

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial

namespace NaculichRegge

/-- Naculich, Sec. 2 and Sec. 4 (footnote 6): for `ℓ ≥ 2`, every `ℓ`-loop Regge colour factor
`N^{ℓ−i} C_{ik}` satisfies the four group-theory constraints (2.14)/(2.15), i.e. is orthogonal to
the four `ℓ`-loop null vectors, and has vanishing `t_2^{(ℓ)}` (leading-colour `c[2]`) component. -/
theorem regge_color_null_constraints (ℓ i k : ℕ) (hℓ : 2 ≤ ℓ) (h : IsReggeIndex i k)
    (hi : i ≤ ℓ) :
    (∀ r : Fin 4, ∑ lam ∈ Finset.Icc 1 (3 * ℓ + 3),
        nullVector ℓ r lam * extCoord ℓ ((X : ℂ[X]) ^ (ℓ - i) • reggeColor i k) lam = 0) ∧
      extCoord ℓ ((X : ℂ[X]) ^ (ℓ - i) • reggeColor i k) 2 = 0 := by sorry

end NaculichRegge
