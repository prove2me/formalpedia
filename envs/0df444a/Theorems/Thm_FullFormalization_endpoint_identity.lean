-- Prove2me | Theorems.Thm_FullFormalization_endpoint_identity
-- name    : FullFormalization.endpoint_identity
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-09T05:55:36.813278+00:00
-- url     : https://prove2.me/theorems/dfd67378-ce72-4e1c-9ea3-a12044cd3a32
-- title:
--   Endpoint identity (11.2) for the master certificate
-- statement:
--   Let $N \ge 1$, let $x, g : \mathbb{N} \to E$ be the iterate and gradient sequences of the rational-NAG run on an admissible function, let $F : \mathbb{N} \to \mathbb{R}$ be the corresponding objective values, and let $r \in E$ be the initial displacement. Then the endpoint identity holds exactly:
--   $$ F_N \;-\; \tau_N\,\|r\|^{2} \;-\; V_N \;+\; b_N\, I_{\star,N} \;=\; 0, \qquad \text{i.e.}\qquad \tau_N\|r\|^{2} - F_N \;=\; -V_N + b_N\, I_{\star,N}, $$
--   where $\tau_N = 2/(N^{2}+7N+4)$ is the target constant, $V_N$ is the terminal local potential (8.5), $b_N$ is the terminal interpolation weight (4.4), and $I_{\star,N} = I_{0,N}$ is the smooth-convex residual (2.1) between $x_N$ and the origin $x_\star = 0$. This is the last of the four local identities summed by the master telescoping certificate (7.1).
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §11, eq. (11.2); Lean: FullFormalization.CertificateIdentities lines 167–174

-- Generated from F:/20261008/FullFormalization\FullFormalization\CertificateIdentities.lean (Phase 3): skeleton subtraction, proof cut at
-- valStart (Stage 2), docstring stripped, declaration hoisted to top
-- level with its fully dotted name; body is `:= by sorry`.
/-
  FullFormalization.CertificateIdentities

  Source sections 9-12: the local certificate identities and the master
  telescoping certificate.

  The identities are exact algebraic identities between quadratic forms in a
  few vectors and their function values.  They are *not* inequalities and no
  numerical testing is involved.  The relations that the source uses to
  eliminate the accumulated weights are stated abstractly, with free scalars:

    (10.6)  A = (B E - h)/D          (from  a_{j-1} D_j = a_j D_{j+1} - h_j)
    (10.7)  h_{j+1} = (h - 1)/m      (from  h_j = 1 + m_j h_{j+1})
    (10.8)  F = E - 1 - m (D - E)    (this is (5.6), the D recurrence)
    (10.9)  C = (B E + h_{j+1})/F    (from  a_{j+1} D_{j+2} = a_j D_{j+1} + h_{j+1})

  Proving the abstract form and then instantiating is exactly the source's own
  strategy (section 10.1 introduces the abstract parameters `D, E, F, h, m,
  A, B, C` and works with them); the instantiation uses `CoefficientIdentities`.

  Scalar names are `A B C Dd Ee Ff hh m` throughout this file, to avoid
  shadowing the ambient type variable `E`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Theorems.Thm_FullFormalization_a_last
import Theorems.Thm_FullFormalization_b_eq

open scoped Gradient RealInnerProductSpace
open Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Abstract coefficient functions (source (8.1), (8.2), (6.3)-(6.4)) -/




















/-! ### Source (11.2): the endpoint identity

`τ‖r‖² - F_N = -V_N + b_N I_{⋆,N}`, equivalently `F_N - τ‖r‖² - V_N + b_N I_{⋆,N} = 0`.
This is a direct algebraic consequence of (8.5) and `b_N = 1 - a_{N-1}`
(source line 1264) — no geometry is involved. -/



/-! ### Source (11.1): the terminal identity

`V_N - V_{N-1} = -b_{N-1} I_{⋆,N-1} - a_{N-1} I_{N-1,N} - S_{N-1}`.

**Geometry.**  The source's prose labels the local vectors `p = y_{N-1}`,
`q = y_N`, but its formulas (11.3)-(11.4) are the Nesterov recurrences only
under the reading `y_{N-1}` for `q` and `y_{N-2}` for `p`; with that reading the
pair fed to `Q_{N-1}` is `(y_{N-1}, y_N)`, which is also what the source's own
cross-check script uses.  Concretely the source's (11.3)-(11.4) read

    x_{N-1} = (1 + m_{N-2}) y_{N-1} - m_{N-2} y_{N-2}
    y_N     = x_{N-1} - g_{N-1}
    x_N     = (1 + m_{N-1}) y_N - m_{N-1} y_{N-1}

which is exactly how the hypothesis set below is stated.  The identity is
confirmed by exact rational point evaluation for several `N` in
`scripts/verify_concrete_rigorous.py`.

**Proof.**  The geometry hypotheses eliminate `x_{N-1}`, `x_N` and `y_N`
(only `x_{N-1} = y_N + g_{N-1}` is used, so `m_{N-2}` and `y_{N-2}` disappear).
The coefficient identities of `CoefficientIdentities` then replace `b_N`,
`b_{N-1}`, `h_{N-1}`, `a_{N-1}`, `a_{N-2}`, `D_N`, `D_{N-1}` and `mom_{N-1}`
by closed forms; the remaining identity is a polynomial in `N` and in the six
vector atoms `‖y_{N-1}‖², ‖y_N‖², ⟪y_{N-1}, y_N⟫, ‖g_{N-1}‖², ‖g_N‖²,
⟪g_{N-1}, g_N⟫, …`, which `field_simp`/`ring` close.

The algebraic content is a single scalar relation between the terminal local
parameters.  Writing `a = a_{N-1}`, `m = m_{N-1}`, `P = D_N`, `Q = D_{N-1}`
the identity is equivalent to `P (a - m - 1) + Q m + 1 = 0`; this follows from
`D_N = d_N + (N+3)/4` and `D_{N-1} - D_N = (N+2)/4 = m (N+2)^2/4` with
`m (N+2) = N - 1`, since it collapses to `1 - (N+3)/4 + (N-1)/4 = 0`. -/



/-! ### Source (10.1): the interior identity, in concrete coefficients

`V_{j+1} - V_j = -b_j I_{j,j+1} - a_j I_{⋆,j} - S_j`, i.e. the same
decrement as the terminal identity but for `1 <= j <= N-2`.

**Geometry.**  The local data are `u = y_j`, `v = y_{j+1}`, `g_j`, `g_{j+1}`,
and the source's (10.2)-(10.4) read

    x_j     = y_{j+1} + g_j
    x_{j+1} = (1 + m_j) y_{j+1} - m_j y_j
    y_{j+2} = x_{j+1} - g_{j+1}

(the first being `y_{j+1} = x_j - g_j` rearranged).  Note that `hxj` is *not*
`x_j = y_j + g_j`: the interior decrement is measured between `V_j` and
`V_{j+1}`, so the point whose residual is `I_{⋆,j}` is `x_j`, and by (10.2)
that point equals `y_{j+1} + g_j`, not `y_j + g_j`.  Exact rational point
evaluation rejects the `y_j` reading, so the statement below uses `y (j+1)`.

This is the concrete instantiation of `interior_identity_abstract` (source
(10.1)) with `A = a_{j-1}, B = a_j, C = a_{j+1}, Dd = D_j, Ee = D_{j+1},
Ff = D_{j+2}, hh = h_j, m = m_j`; the `-τ‖r‖²` term cancels between the two
`Vterm`s, which is why only the difference appears.  The proof mirrors that of
`terminal_identity`: eliminate the geometry, replace every coefficient by its
closed form using `CoefficientIdentities`, normalise the inner products, and
close with `field_simp`/`ring`. -/



end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
open Set
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem FullFormalization.endpoint_identity (N : ℕ) (hN : 1 ≤ N) (r : E) (x g : ℕ → E) (Fv : ℕ → ℝ) :
    Fv N - tau N * ‖r‖ ^ 2 - VN N r x g Fv + b N N * Istar (Fv N) (x N) (g N) = 0 := by sorry
