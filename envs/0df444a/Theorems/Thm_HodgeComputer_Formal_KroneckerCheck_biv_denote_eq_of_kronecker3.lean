-- Prove2me | Theorems.Thm_HodgeComputer_Formal_KroneckerCheck_biv_denote_eq_of_kronecker3
-- name    : HodgeComputer.Formal.KroneckerCheck.biv_denote_eq_of_kronecker3
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:27:08.159065+00:00
-- url     : https://prove2.me/theorems/9267e025-fd9f-492f-801e-4407a3c97b81
-- title:
--   Soundness of 3-variable Kronecker verification for sparse bivariate polynomials
-- statement:
--   Let $K$ be a commutative ring, $v : \mathbb{N} \to K$, $x, y \in K$, $d_0, d_1, d_2, b \in \mathbb{N}$, and $p, q$ two sparse bivariate polynomial ASTs (`Biv`). If the computable boolean checker succeeds:
--
--   $$\operatorname{checkBivEq3}(d_0, d_1, d_2, b, p, q) = \mathrm{true},$$
--
--   then $\operatorname{denote}(v, x, y, p) = \operatorname{denote}(v, x, y, q)$ in $K$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/PolynomialEncoding/KroneckerCheck.lean#L1026-L1108

import Definitions.Def_HodgeComputerFormal_PolyEncoding
set_option autoImplicit false

theorem HodgeComputer.Formal.KroneckerCheck.biv_denote_eq_of_kronecker3
    {K : Type*} [CommRing K]
    (v : ℕ → K) (x y : K) (d0 d1 d2 b : ℕ)
    (p q : PolynomialEncoding.BivariateExpressions.Biv)
    (h : PolynomialEncoding.KroneckerCheck.checkBivEq3 d0 d1 d2 b p q = true) :
    PolynomialEncoding.BivariateExpressions.denote v x y p =
      PolynomialEncoding.BivariateExpressions.denote v x y q := by sorry
