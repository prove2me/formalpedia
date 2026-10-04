-- Prove2me | Theorems.Thm_HardyFiveAxioms_qutrit_D_matrix
-- name    : HardyFiveAxioms.qutrit_D_matrix
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T00:28:32.810809+00:00
-- url     : https://prove2.me/theorems/784d9728-fbbb-4fc6-9042-293edb5374f3
-- title:
--   $N=3$: the $9\times9$ matrix $D$ with $h=\tfrac12$, $q=\tfrac14$
-- statement:
--   For $N=3$, order the fiducial projectors (26)–(27) as
--
--   $$1,\ 2,\ 3,\ 12x,\ 12y,\ 13x,\ 13y,\ 23x,\ 23y .$$
--
--   Then the matrix $D_{ij}=\mathrm{tr}(\hat P_i\hat P_j)$ is
--
--   $$D=\begin{pmatrix}
--   1&0&0&h&h&h&h&0&0\\
--   0&1&0&h&h&0&0&h&h\\
--   0&0&1&0&0&h&h&h&h\\
--   h&h&0&1&h&q&q&q&q\\
--   h&h&0&h&1&q&q&q&q\\
--   h&0&h&q&q&1&h&q&q\\
--   h&0&h&q&q&h&1&q&q\\
--   0&h&h&q&q&q&q&1&h\\
--   0&h&h&q&q&q&q&h&1
--   \end{pmatrix},\qquad h=\tfrac12,\ q=\tfrac14 .$$
--
--   In Section 8.7 Hardy derives this matrix from the axioms and states that "the projection operators which give rise to this $D$ are, up to arbitrary choices in phase, those in equations (26) and (27)". This milestone checks that statement.
--
--   **Formalization Note** Indices are $0$-based. The equality is entrywise in $\mathbb C$.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, pp. 22–23, Section 8.7 (the $9\times9$ matrix $D$ with $h=1/2$, $q=1/4$)

import Mathlib
import Definitions.Def_hardy2001_projectors

namespace HardyFiveAxioms

/-- Hardy 2001, Section 8.7: for `N = 3` with fiducial order
`1, 2, 3, 12x, 12y, 13x, 13y, 23x, 23y`, the matrix `Dᵢⱼ = tr(P̂ᵢP̂ⱼ)` of the projectors
(26)–(27) has the stated form with `h = 1/2` and `q = 1/4`. -/
theorem qutrit_D_matrix :
    let P : Fin 9 → Matrix (Fin 3) (Fin 3) ℂ :=
      ![proj (ket 0), proj (ket 1), proj (ket 2),
        proj (ketX 0 1), proj (ketY 0 1), proj (ketX 0 2), proj (ketY 0 2),
        proj (ketX 1 2), proj (ketY 1 2)]
    let h : ℝ := 1 / 2
    let q : ℝ := 1 / 4
    let D : Matrix (Fin 9) (Fin 9) ℝ :=
      !![1, 0, 0, h, h, h, h, 0, 0;
         0, 1, 0, h, h, 0, 0, h, h;
         0, 0, 1, 0, 0, h, h, h, h;
         h, h, 0, 1, h, q, q, q, q;
         h, h, 0, h, 1, q, q, q, q;
         h, 0, h, q, q, 1, h, q, q;
         h, 0, h, q, q, h, 1, q, q;
         0, h, h, q, q, q, q, 1, h;
         0, h, h, q, q, q, q, h, 1]
    ∀ i j : Fin 9, (P i * P j).trace = (D i j : ℂ) := by sorry

end HardyFiveAxioms
