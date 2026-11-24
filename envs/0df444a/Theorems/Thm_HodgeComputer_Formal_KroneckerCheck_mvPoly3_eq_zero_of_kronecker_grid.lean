-- Prove2me | Theorems.Thm_HodgeComputer_Formal_KroneckerCheck_mvPoly3_eq_zero_of_kronecker_grid
-- name    : HodgeComputer.Formal.KroneckerCheck.mvPoly3_eq_zero_of_kronecker_grid
-- status  : Proved
-- author  : @benediamond
-- created : 2026-11-24T03:28:33.16873+00:00
-- url     : https://prove2.me/theorems/31c2d5ce-3983-4a04-acec-478afc888904
-- title:
--   Soundness of 1D Kronecker × 2D grid evaluation for 3-variable integer polynomials
-- statement:
--   Let $p \in \mathbb{Z}[S, Q, T]$ respect the degree and coefficient-mass bound $b = (d_S, d_Q, d_T, M)$ on $[-Q_{\max}, Q_{\max}] \times [-T_{\max}, T_{\max}]$. Suppose $Q_{\mathrm{pts}}, T_{\mathrm{pts}} \subset \mathbb{Z}$ are finite sets with
--
--   $$|Q_{\mathrm{pts}}| > d_Q,\quad \forall q \in Q_{\mathrm{pts}},\, |q| \le Q_{\max},\qquad |T_{\mathrm{pts}}| > d_T,\quad \forall t \in T_{\mathrm{pts}},\, |t| \le T_{\max},$$
--
--   and $B > M$. If $p(B, q, t) = 0$ for all $(q, t) \in Q_{\mathrm{pts}} \times T_{\mathrm{pts}}$, then $p = 0$ in $\mathbb{Z}[S, Q, T]$.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/PolynomialEncoding/KroneckerCheck.lean#L1429-L1578

import Definitions.Def_HodgeComputerFormal_PolyEncoding
set_option autoImplicit false

theorem HodgeComputer.Formal.KroneckerCheck.mvPoly3_eq_zero_of_kronecker_grid
    (p : PolynomialEncoding.KroneckerCheck.P3Z)
    (b : PolynomialEncoding.KroneckerCheck.PB) (Qmax Tmax B : ℕ)
    (Q_pts T_pts : Finset ℤ)
    (hR : PolynomialEncoding.KroneckerCheck.RespectsBound Qmax Tmax p b)
    (hQ_deg : b.dQ < Q_pts.card) (hQ_bd : ∀ q ∈ Q_pts, q.natAbs ≤ Qmax)
    (hT_deg : b.dT < T_pts.card) (hT_bd : ∀ t ∈ T_pts, t.natAbs ≤ Tmax)
    (hB : b.M < B)
    (hev : ∀ q ∈ Q_pts, ∀ t ∈ T_pts,
      MvPolynomial.eval (PolynomialEncoding.KroneckerCheck.v3Int (B : ℤ) q t) p = 0) :
    p = 0 := by sorry
