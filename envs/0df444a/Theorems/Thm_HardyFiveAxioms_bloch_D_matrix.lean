-- Prove2me | Theorems.Thm_HardyFiveAxioms_bloch_D_matrix
-- name    : HardyFiveAxioms.bloch_D_matrix
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T00:09:09.612407+00:00
-- url     : https://prove2.me/theorems/ceba8d13-f768-4cd3-9afb-d10be97f60eb
-- title:
--   Bloch sphere: $D_{ij}=\mathrm{tr}(\hat P_i\hat P_j)$ for $N=2$ with $a=b=c=\tfrac12$
-- statement:
--   For $N=2$, take the fiducial projectors $\hat P_1=|1\rangle\langle1|$, $\hat P_2=|2\rangle\langle2|$, $\hat P_3=|12\rangle_x\langle12|$, $\hat P_4=|12\rangle_y\langle12|$ of Eqs. (26)–(27). Then the matrix $D_{ij}=\mathrm{tr}(\hat P_i\hat P_j)$ of Eq. (18) is
--
--   $$D=\begin{pmatrix}1&0&\tfrac12&\tfrac12\\0&1&\tfrac12&\tfrac12\\\tfrac12&\tfrac12&1&\tfrac12\\\tfrac12&\tfrac12&\tfrac12&1\end{pmatrix},$$
--
--   which is Eq. (87), the choice $a=b=c=\tfrac12$ for which the pure-state surface is the Bloch sphere.
--
--   **Formalization Note** Indices are $0$-based. The equality is entrywise in $\mathbb C$, with the real entries cast to complex numbers.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 7, Eq. (18); p. 8, Eqs. (26)–(27); p. 22, Section 8.6, Eq. (87)

import Mathlib
import Definitions.Def_hardy2001_projectors

namespace HardyFiveAxioms

/-- Hardy 2001, Eq. (87) (with Eqs. (18), (26)–(27)): for `N = 2` and the fiducial projectors
`|1⟩⟨1|`, `|2⟩⟨2|`, `|12⟩ₓ⟨12|`, `|12⟩_y⟨12|`, the matrix `Dᵢⱼ = tr(P̂ᵢP̂ⱼ)` is the
Bloch-sphere matrix with `a = b = c = 1/2`. -/
theorem bloch_D_matrix :
    let P : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
      ![proj (ket 0), proj (ket 1), proj (ketX 0 1), proj (ketY 0 1)]
    ∀ i j : Fin 4, (P i * P j).trace =
      ((!![1, 0, 1 / 2, 1 / 2;
           0, 1, 1 / 2, 1 / 2;
           1 / 2, 1 / 2, 1, 1 / 2;
           1 / 2, 1 / 2, 1 / 2, 1] : Matrix (Fin 4) (Fin 4) ℝ) i j : ℂ) := by sorry

end HardyFiveAxioms
