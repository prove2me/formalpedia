-- Prove2me | Theorems.Thm_NumInvQH_Oblique_range_fact_4_3
-- name    : NumInvQH.Oblique.range_fact_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:52.199255+00:00
-- url     : https://prove2.me/theorems/b88fa8e6-b629-4f3a-97c3-5a9a5f2f6268
-- title:
--   Proof of Theorem 4.3 (p. 16) — $\tilde c^{SV\star}\in R(\tilde c^{S\star})$: a PSD block matrix $\begin{pmatrix}C&u\\u^{\mathsf T}&\gamma\end{pmatrix}$ has $u\in R(C)$
-- statement:
--   Let $C\in\mathbb R^{d\times d}$, $u\in\mathbb R^d$ and $\gamma\in\mathbb R$. If the $(d+1)\times(d+1)$ block matrix
--
--   $$\begin{pmatrix}C & u\\ u^{\mathsf T} & \gamma\end{pmatrix}$$
--
--   is positive semidefinite, then $u\in R(C)$, the column space of $C$.
--
--   In the paper, $C=\tilde c^{S\star}$, $u=\tilde c^{SV\star}$ and the block matrix is the modified second characteristic of the joint process $(S,V)$, which is positive semidefinite. The proof of Theorem 4.3 uses the resulting fact $\tilde c^{SV\star}\in R(\tilde c^{S\star})$ to conclude that the pure-hedge argmin $\Xi_\xi$ in (4.7) is non-empty; it is the hypothesis $u\in R(C)$ of the pointwise statement of Theorem 4.3.
--
--   **Formalization Note** The block matrix is `Matrix.fromBlocks` with a $1\times1$ lower-right block; positive semidefiniteness is Mathlib's `Matrix.PosSemidef` (which includes symmetry). The paper asserts the range fact in one sentence without a separate argument.
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, p. 16, proof of Theorem 4.3

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

namespace NumInvQH.Oblique

/-- The range assertion in the proof of Theorem 4.3 follows from joint PSD. -/
theorem range_fact_4_3 {d : ℕ}
    (C : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) (γ : ℝ)
    (hJoint : (Matrix.fromBlocks C (Matrix.of (fun i (_ : Fin 1) => u i))
      (Matrix.of (fun (_ : Fin 1) j => u j))
      (Matrix.of (fun (_ _ : Fin 1) => γ))).PosSemidef) :
    u ∈ LinearMap.range (Matrix.toLin' C) := by sorry

end NumInvQH.Oblique
