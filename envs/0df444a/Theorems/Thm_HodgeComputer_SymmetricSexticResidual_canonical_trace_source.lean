-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_canonical_trace_source
-- name    : HodgeComputer.SymmetricSexticResidual.canonical_trace_source
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-09T03:48:03.670758+00:00
-- url     : https://prove2.me/theorems/b0bcfd4c-df00-43b3-9114-86ccae7d0db6
-- title:
--   Symmetric sextic: exact canonical trace-source coefficients
-- statement:
--   For the reflection chart of the symmetric sextic, let $\lambda,b,c,d,u\in\mathbb C$. Put $L=1+2b$, $R=c^2+2cd$, and define
--
--   $$
--   \begin{aligned}
--   \ell&=2+2\lambda^6-\frac57\lambda^2-\frac{10}{7}\lambda^4,\\
--   B&=30+30\lambda^4c^2+\frac57(R+2\lambda^2L)
--    +\frac{10}{7}(\lambda^4L+2\lambda^2R),\\
--   C&=30+30\lambda^2c^4+\frac57(-\lambda^2L^2-2LR)
--    +\frac{10}{7}(-2\lambda^2LR-R^2),\\
--   D&=2+b^6+2c^6+d^6+\frac57L^2R+\frac{10}{7}LR^2.
--   \end{aligned}
--   $$
--
--   Write $f=\ell u^3+Bu^2+Cu+D$ and $P=bd(1-u)(c^2-\lambda^2u)$, with all derivatives below taken in $u$. These are the exact weighted equation and numerator obtained from the chart $X=(1+v,1-v,b)$, $Y=(c+\lambda v,c-\lambda v,d)$ with $u=v^2$.
--
--   Assume $\ell\ne0$. Set
--
--   $$
--   \begin{gathered}
--   p_0=bdc^2,\qquad p_1=-bd(c^2+\lambda^2),\qquad p_2=bd\lambda^2,\\
--   \kappa=\frac{p_2}{3\ell},\qquad
--   T_0=\frac{3\ell p_0-p_2C}{3\ell},\qquad
--   T_1=\frac{3\ell p_1-2p_2B}{3\ell}.
--   \end{gathered}
--   $$
--
--   The canonical source is linear in the normal coordinate:
--
--   $$
--   P-\kappa f_u=T_0+T_1u,\qquad P_u-\kappa f_{uu}=T_1.
--   $$
--
--   Consequently its residue numerator satisfies
--
--   $$
--   f_uP_u-f_{uu}P=f_uT_1-f_{uu}(T_0+T_1u).
--   $$
--
--   The coefficients $T_0,T_1$ depend only on $(\lambda,b,c,d)$. They specify the two source traces required by the existing conditional trace-descent construction for the symmetric-sextic-residual mission. This is an exact supporting identity; it does not construct an upstairs current, a relative primitive, or a certificate.
-- source:
--   fqlx, PR #222 at d0919c2f5daf105f41f69887318a2677f0dfbc66: https://github.com/fqlx/sextics/blob/d0919c2f5daf105f41f69887318a2677f0dfbc66/data/symmetric-sextic-residual/SymmetricTraceEndpoint.lean, definitions normalCorrection/targetSource0/targetSource1; exact coefficient continuation prepared for kmehltretter82 with OpenAI Codex assistance. https://github.com/kmehltretter82/sextics/blob/8ca8f3ae2c0e17dd59ba4067f069758ba962c39a/data/symmetric-sextic-residual/SymmetricTraceFormula.lean

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false

theorem HodgeComputer.SymmetricSexticResidual.canonical_trace_source
    (lam b c d u : ℂ) :
    let L := 1 + 2*b
    let R := c^2 + 2*c*d
    let ell := 2 + 2*lam^6 - (5/7 : ℂ)*lam^2 - (10/7 : ℂ)*lam^4
    let B := 30 + 30*lam^4*c^2 + (5/7 : ℂ)*(R + 2*lam^2*L) +
      (10/7 : ℂ)*(lam^4*L + 2*lam^2*R)
    let C := 30 + 30*lam^2*c^4 + (5/7 : ℂ)*(-lam^2*L^2 - 2*L*R) +
      (10/7 : ℂ)*(-2*lam^2*L*R - R^2)
    let D := 2 + b^6 + 2*c^6 + d^6 + (5/7 : ℂ)*L^2*R + (10/7 : ℂ)*L*R^2
    let P := b*d*(1-u)*(c^2-lam^2*u)
    let Pu := b*d*(-c^2-lam^2+2*lam^2*u)
    let g := 3*ell*u^2 + 2*B*u + C
    let gu := 6*ell*u + 2*B
    let T0 := b*d*c^2 - b*d*lam^2*C/(3*ell)
    let T1 := -b*d*(c^2+lam^2) - 2*b*d*lam^2*B/(3*ell)
    ell ≠ 0 →
      (2 + b^6 + 2*c^6 + d^6 + 30*u + 30*u^2 + 2*u^3 +
        30*lam^2*c^4*u + 30*lam^4*c^2*u^2 + 2*lam^6*u^3 +
        (5/7 : ℂ)*(L-u)^2*(R-lam^2*u) +
        (10/7 : ℂ)*(L-u)*(R-lam^2*u)^2 = ell*u^3+B*u^2+C*u+D) ∧
      (P - (b*d*lam^2/(3*ell))*g = T0+T1*u) ∧
      (Pu - (b*d*lam^2/(3*ell))*gu = T1) ∧
      (g*Pu-gu*P = g*T1-gu*(T0+T1*u)) := by sorry
