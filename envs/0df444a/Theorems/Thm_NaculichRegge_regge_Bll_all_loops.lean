-- Prove2me | Theorems.Thm_NaculichRegge_regge_Bll_all_loops
-- name    : NaculichRegge.regge_Bll_all_loops
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:24:21.520091+00:00
-- url     : https://prove2.me/theorems/b76cddb9-a18e-4aa0-bf33-1281c4be7358
-- title:
--   All-loop formula for $B^{(\ell)}_{\ell\ell}$ (even $\ell$, and $\ell=1$)
-- statement:
--   Write the $\ell$-loop four-gluon amplitude in the Regge basis, $\mathcal A^{(\ell)}=A_1^{(0)}\tilde a^\ell\sum_{i=0}^{\ell}\sum_k B^{(\ell)}_{ik}N^{\ell-i}C_{ik}$, and let $A^{(\ell)}_\lambda$ ($1\le\lambda\le3\ell+3$) be its colour-ordered amplitudes, i.e. its coordinates in the extended trace basis. Then for every even $\ell\ge0$
--   $$A_1^{(0)}\tilde a^\ell\,B^{(\ell)}_{\ell\ell}=\frac{1}{2\cdot3^{\ell/2}}\Big(A^{(\ell)}_{3\ell+1}-A^{(\ell)}_{3\ell+3}\Big),$$
--   and for $\ell=1$
--   $$A_1^{(0)}\tilde a\,B^{(1)}_{11}=-\big(A^{(1)}_1+A^{(1)}_3\big).$$
--   The prefactor $A_1^{(0)}\tilde a^\ell$ is an arbitrary complex number $\kappa$ and the coefficients $B_{ik}$ are arbitrary complex numbers.
-- source:
--   S. G. Naculich, "All-loop-orders relation between Regge limits of N = 4 SYM and N = 8 supergravity four-point amplitudes", arXiv:2012.00030v2, https://arxiv.org/abs/2012.00030, p. 16, eqs. (4.26)–(4.27)

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial

namespace NaculichRegge

/-- Naculich, eqs. (4.26)–(4.27): the coefficient `B_{ℓℓ}` of the most-subleading Regge colour
factor, for every even loop order `ℓ` and for `ℓ = 1`. -/
theorem regge_Bll_all_loops (ℓ : ℕ) (κ : ℂ) (B : ℕ × ℕ → ℂ) :
    (Even ℓ → κ * B (ℓ, ℓ) =
        (colorOrderedAmp ℓ κ B (3 * ℓ + 1) - colorOrderedAmp ℓ κ B (3 * ℓ + 3)) /
          (2 * 3 ^ (ℓ / 2))) ∧
    (ℓ = 1 → κ * B (1, 1) = -(colorOrderedAmp 1 κ B 1 + colorOrderedAmp 1 κ B 3)) := by sorry

end NaculichRegge
