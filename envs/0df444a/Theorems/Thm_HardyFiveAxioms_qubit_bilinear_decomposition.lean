-- Prove2me | Theorems.Thm_HardyFiveAxioms_qubit_bilinear_decomposition
-- name    : HardyFiveAxioms.qubit_bilinear_decomposition
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T23:28:05.790145+00:00
-- url     : https://prove2.me/theorems/92ba3e80-cf0f-4bed-9409-c1927739a2e0
-- title:
--   Qubit: $r^TDr'=\vec v^{\,T}A\vec v\,'+\mu\mu'/2$
-- statement:
--   Let $a,b,c\in\mathbb R$, let $v=(v_0,v_1,v_2,v_3)$ and $v'=(v_0',v_1',v_2',v_3')$ be real vectors, and put $r=Cv$ and $r'=Cv'$, with $C$ as in Eq. (78). Then
--
--   $$r^TD\,r'=\vec v^{\,T}A\,\vec v\,'+\frac{\mu\mu'}2,$$
--
--   where $\vec v=(v_1,v_2,v_3)$, $\vec v\,'=(v_1',v_2',v_3')$, $D$ is the matrix (74), $A$ is the matrix (83), and
--
--   $$\mu=2v_0+v_1+v_2+v_3,\qquad \mu'=2v_0'+v_1'+v_2'+v_3'$$
--
--   are the normalization coefficients of Eq. (80).
--
--   This is Eq. (81) of the paper, the identity that turns the pure-state condition $r^TDr=1$ for normalized states into the quadric $\vec v^{\,T}A\vec v=\tfrac12$ (Eq. (84)).
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 21, Section 8.6, Eqs. (76)–(83)

import Mathlib
import Definitions.Def_hardy2001_qubit

namespace HardyFiveAxioms

open Matrix

/-- Hardy 2001, Section 8.6, Eqs. (76)–(83): writing `r = C v`, `r' = C v'`, the bilinear
form satisfies `rᵀ D r' = v⃗ᵀ A v⃗' + μ μ'/2`, where `v⃗ = (v₁, v₂, v₃)` and
`μ = 2v₀ + v₁ + v₂ + v₃` is the normalization coefficient (Eq. (80)). -/
theorem qubit_bilinear_decomposition (a b c : ℝ) (v w : Fin 4 → ℝ) :
    (qubitC *ᵥ v) ⬝ᵥ (qubitD a b c *ᵥ (qubitC *ᵥ w)) =
      ![v 1, v 2, v 3] ⬝ᵥ (qubitA a b c *ᵥ ![w 1, w 2, w 3]) +
        (2 * v 0 + v 1 + v 2 + v 3) * (2 * w 0 + w 1 + w 2 + w 3) / 2 := by sorry

end HardyFiveAxioms
