-- Prove2me | Theorems.Thm_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j
-- name    : ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/a018afe1-b6a1-5bc6-9ca1-45f1783da9ea
-- title:
--   Fibre of Φ₂ over j(E) splits over the Vélu 2-quotients
-- statement:
--   Let $K$ be a field in which $2 \neq 0$ and let $W$ be a Weierstrass curve over $K$ that is elliptic (its discriminant is a unit). Let $\iota$ be a finite index type of cardinality $3$ and $P \colon \iota \to K \times K$ an injective family of pairs such that, writing $P i = (x_i, y_i)$: each $(x_i,y_i)$ satisfies the affine Weierstrass equation of $W$; each satisfies $W.\mathrm{veluGy}(x_i,y_i) = -(2y_i + a_1 x_i + a_3) = 0$, so the three points are the nontrivial $2$-torsion points; and the Weierstrass curve $W.\mathrm{veluQuotient2}(x_i,y_i)$, namely the curve with the same $a_1,a_2,a_3$ and with $a_4$ replaced by $a_4 - 5t_i$ and $a_6$ by $a_6 - b_2 t_i - 7 x_i t_i$, where $t_i = W.\mathrm{veluGx}(x_i,y_i) = 3x_i^2 + 2a_2 x_i + a_4 - a_1 y_i$, has nonvanishing discriminant $\Delta \neq 0$ (whence it too is elliptic, so has a $j$-invariant). Then the polynomial $\mathrm{fibrePoly}\ \Phi_2\ j(W) \in K[X]$, obtained from the level-$2$ classical modular polynomial $\Phi_2 \in \mathbb{Z}[X][Y]$ by evaluating each of its coefficient polynomials at $j(W)$, equals $\prod_i \bigl(X - C(j(W.\mathrm{veluQuotient2}(x_i,y_i)))\bigr)$; explicitly, $X^3 + (-j^2 + 1488j - 162000)X^2 + (1488j^2 + 40773375j + 8748000000)X + (j^3 - 162000j^2 + 8748000000j - 157464000000000)$ with $j = j(W)$ splits with the three $2$-isogenous $j$-invariants as roots, counted with multiplicity.
--
--   This is the classical statement that, for an elliptic curve with rational $2$-torsion, the fibre of the modular polynomial $\Phi_2$ over $j(E)$ has as its roots exactly the $j$-invariants of the three quotients $E/\langle P \rangle$ by the order-$2$ subgroups, in Vélu's normal form, as an identity of monic cubics. It is the level-$2$ instance of the general statement packaged in [`ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j`](thm.html#ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j), which is what the later treatment of $2$-isogenies and modular curves uses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j.lean

import Mathlib
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_ModularCurve_ClassicalModularPolynomials
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial ModularCurve WeierstrassCurve WeierstrassCurve.Affine

theorem ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j
    {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) (P : ι → K × K) (hP : Function.Injective P)
    (hPeq : ∀ i, W.toAffine.Equation (P i).1 (P i).2) (hPgy : ∀ i, W.veluGy (P i).1 (P i).2 = 0)
    (hΔ : ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0) :
    fibrePoly phiTwo W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _ (W.veluQuotient2 (P i).1 (P i).2)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by sorry
