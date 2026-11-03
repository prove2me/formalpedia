-- Prove2me | Theorems.Thm_Grothendieck_er_root_unique
-- name    : Grothendieck.er_root_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T04:16:11.273279+00:00
-- url     : https://prove2.me/theorems/a099c76d-64f8-4b66-bf5d-0aaec1fa2ea0
-- title:
--   Proposition 3.3 — $E_r$ has exactly one root in the unit disc
-- statement:
--   Let $r\ge1$ and let $E_r(z)=C_rz\,{}_2F_1(1/2,1/2;r/2+1;z^2)$ be the analytic extension of $E_r$ to the unit disc $D=\{z\in\mathbb C:\lVert z\rVert<1\}$. Then $E_r$ has exactly one root in $D$, and this root is simple and located at the origin:
--
--   $$
--   E_r(0)=0,\qquad E_r'(0)=C_r\neq0,\qquad\text{and}\qquad E_r(z)=0\ \text{with}\ \lVert z\rVert<1\ \Longrightarrow\ z=0 .
--   $$
--
--   Two facts are asserted: the only zero of $E_r$ in the open unit disc is $0$, and that zero is simple (equivalently, $E_r'(0)=C_r\neq0$). The proof is by Rouché's theorem, comparing $E_r$ with the linear function $C_rz$ on the boundary circle: the Taylor coefficients of $E_r$ are nonnegative and sum to $E_r(1)=1$, and $C_r>1/2$, so the remainder has modulus strictly smaller than $\lvert C_rz\rvert$ there.
--
--   **Formalization Note** The two claims are combined into a single statement about `ErComplex r`, the series $\sum_k a_{2k+1}z^{2k+1}$ in $\mathbb C$, together with `deriv (ErComplex r) 0 = (Cr r : ℂ)` and `Cr r ≠ 0`.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, Proposition 3.3, p. 88. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib
import Definitions.Def_Grothendieck_Series

namespace Grothendieck

theorem er_root_unique (r : ℕ) (hr : 1 ≤ r) :
    (∀ z : ℂ, ‖z‖ < 1 → (ErComplex r z = 0 ↔ z = 0)) ∧
      deriv (ErComplex r) 0 = (Cr r : ℂ) ∧ Cr r ≠ 0 := by sorry

end Grothendieck
