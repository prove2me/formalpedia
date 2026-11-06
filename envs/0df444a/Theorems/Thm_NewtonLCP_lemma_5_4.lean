-- Prove2me | Theorems.Thm_NewtonLCP_lemma_5_4
-- name    : NewtonLCP.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:28:45.051607+00:00
-- url     : https://prove2.me/theorems/19cc30ca-d4d6-4d13-8a7d-729210fb32d1
-- title:
--   Lemma 5.4 — $\zeta(H)<6$ and $\|Q_HHQ_H^{-1}\|_{\max}\le K$
-- statement:
--   For $A\in\mathcal P_\star\cap\mathbb R^{n\times n}$ let $H=(I_n+A)^{-1}$. Then $\zeta(H)<6$, and the Rump weights $q_H$ (with $K=8$) rescale $H$ to a matrix with bounded entries:
--
--   $$\|Q_HHQ_H^{-1}\|_{\max}=\max_{i,j}\frac{q_H(i)\,|H_{ij}|}{q_H(j)}\le K .$$
--
--   The bounded rescaled matrix is what makes the Rump norm independent of the handicap number.
--
--   Differences from the source:
--   - reading: ζ(H) < 6, and thus q_H is well-defined → ζ(H) < 6, with no separate well-definedness clause; reason: q_H is defined by the maximum over simple paths (Definition 5.2), which exists for every H; well-definedness of the walk maximum of Theorem 2.11 has no further content in this definition
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Lemma 5.4, p.14

import Mathlib
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_NewtonLCP_Rump
import Definitions.Def_NewtonLCP_RumpWeight

namespace NewtonLCP

/-- **Lemma 5.4**. Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Lemma 5.4, p.14.

For `A ∈ P⋆ ∩ ℝⁿˣⁿ`, let `H = (Iₙ + A)⁻¹`; then `ζ(H) < 6`, and thus `q_H` is well-defined.
Further, `‖Q_H H Q_H⁻¹‖_max ≤ K` (`K = 8`).

**Formalization Note.** `(Q_H H Q_H⁻¹)ᵢⱼ = q_H(i) Hᵢⱼ / q_H(j)`, so the max-norm bound is
`q_H(i)|Hᵢⱼ|/q_H(j) ≤ 8` for all `i, j`. With the simple-path definition of `q_H` (Definition 5.2)
the weights are always defined, so "`q_H` is well-defined" has no separate Lean content. -/
theorem lemma_5_4 {ι : Type*} [Fintype ι] [DecidableEq ι] (A H : Matrix ι ι ℝ)
    (hA : IsPStar A) (hH : H = (1 + A)⁻¹) :
    cycleMean H < 6 ∧ ∀ i j, rumpWeight H i * |H i j| / rumpWeight H j ≤ 8 := by sorry

end NewtonLCP
