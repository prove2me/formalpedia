-- Prove2me | Theorems.Thm_HodgeComputer_Formal_KroneckerCheck_mvPoly3_eq_zero_of_kronecker2D_gridT
-- name    : HodgeComputer.Formal.KroneckerCheck.mvPoly3_eq_zero_of_kronecker2D_gridT
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:29:46.577399+00:00
-- url     : https://prove2.me/theorems/cfba894c-ad5f-404b-ad74-9facee9d9a55
-- title:
--   Soundness of 2D Kronecker $(B, B^D)$ × 1D $T$-grid verification for $\mathbb{Z}[S, Q, T]$
-- statement:
--   Let $p \in \mathbb{Z}[S, Q, T]$ satisfy `RespectsBound2D D Tmax p b` with $d_S < D$, $M < B$, and let $T_{\mathrm{pts}} \subset \mathbb{Z}$ be a finite set with $|T_{\mathrm{pts}}| > d_T$ and $|t| \le T_{\max}$ for all $t \in T_{\mathrm{pts}}$. If
--
--   $$p(B, B^D, t) = 0 \qquad \forall t \in T_{\mathrm{pts}},$$
--
--   then $p = 0$ in $\mathbb{Z}[S, Q, T]$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/PolynomialEncoding/KroneckerCheck.lean#L1688-L1765

import Definitions.Def_HodgeComputerFormal_PolyEncoding
set_option autoImplicit false

theorem HodgeComputer.Formal.KroneckerCheck.mvPoly3_eq_zero_of_kronecker2D_gridT
    (p : PolynomialEncoding.KroneckerCheck.P3Z)
    (b : PolynomialEncoding.KroneckerCheck.PB) (D Tmax B : ℕ)
    (T_pts : Finset ℤ)
    (hR : PolynomialEncoding.KroneckerCheck.RespectsBound2D D Tmax p b)
    (hS_deg : b.dS < D)
    (hT_deg : b.dT < T_pts.card) (hT_bd : ∀ t ∈ T_pts, t.natAbs ≤ Tmax)
    (hB : b.M < B)
    (hev : ∀ t ∈ T_pts,
      MvPolynomial.eval (PolynomialEncoding.KroneckerCheck.v3Int (B : ℤ) ((B ^ D : ℕ) : ℤ) t) p = 0) :
    p = 0 := by sorry
