-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_norm_le_lmax
-- name    : Gomory69.Asymptotic.norm_le_lmax
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:03:13.557397+00:00
-- url     : https://prove2.me/theorems/fdbb8bce-90e9-4a14-8899-85e5e0055374
-- title:
--   Proof of THEOREM 4, p. 462 — ‖Nx_N*‖ ≤ l_max(D − 1)
-- statement:
--   Let $B$ be a nonsingular integer $m\times m$ matrix, $N$ an integer $m\times n$ matrix, $b\in\mathbb Z^m$, $\mathcal G=M(I)/M(B)$, $\mathcal N$ the set of nonzero $fN_i$, $D=|\det B|$ and $l_{\max}$ the largest Euclidean length of a column $N_i$. If $t^*$ is a vertex of $P(\mathcal G,\mathcal N,fb)$ and $x_N^*$ is the nonbasic part of a vertex of $P_x(B,N,b)$ corresponding to $t^*$ (Remark 1), then
--
--   $$\|Nx_N^*\|=\Bigl\|\sum_{i=1}^{n}N_ix^*_{m+i}\Bigr\|\le l_{\max}(D-1),$$
--
--   where $\|\cdot\|$ is the Euclidean length.
--
--   This is the quantitative core of THEOREM 4: the nonbasic correction moves $b$ by at most $l_{\max}(D-1)$.
--
--   **Formalization Note** No cost or optimality hypothesis is needed for this step; only the vertex property of $t^*$ and conditions (i)–(iii) of Remark 1 enter.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 462, proof of THEOREM 4

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram

namespace Gomory69.Asymptotic

/-- Proof of THEOREM 4 (p. 462): if `t*` is a vertex of `P(𝒢, 𝒩, f b)` and `x_N*` the
nonbasic part of a corresponding vertex (Remark 1), then
`‖N x_N*‖ ≤ l_max (D − 1)`, `D = |det B|`, `‖·‖` the Euclidean length. -/
theorem norm_le_lmax {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (hdet : B.det ≠ 0) (tstar : ↥(groupColumnSet B N) → ℝ)
    (ht : tstar ∈ Set.extremePoints ℝ (groupPolyhedron (groupColumnSet B N) (toGroup B b)))
    (xN : Fin n → ℕ) (hx : IsVertexLift B N tstar xN) :
    euclNorm (fun k => ∑ i, (N k i : ℝ) * (xN i : ℝ)) ≤ lmax N * ((detAbs B : ℝ) - 1) := by sorry

end Gomory69.Asymptotic
