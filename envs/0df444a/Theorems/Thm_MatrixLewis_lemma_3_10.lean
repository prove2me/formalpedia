-- Prove2me | Theorems.Thm_MatrixLewis_lemma_3_10
-- name    : MatrixLewis.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:35.308278+00:00
-- url     : https://prove2.me/theorems/e735b7f7-a309-47f5-b5ec-1637ee8a656a
-- title:
--   Lemma 3.10 — boundary blow-up of $f_q$
-- statement:
--   Throughout, $A_1,\dots,A_m, C$ are real symmetric $n\times n$ matrices, the $A_i$ satisfy Assumption 3.1 (linearly independent, with $\bigcap_i \ker A_i=\{0\}$), and $q>2$ is real; $p=q/(q-2)$ and $p'=q/2$.
--
--   Let $x_k\in\mathcal D$ converge to a point $x_\infty$ of the boundary of $\mathcal D$. Then
--   $$
--   f_q(x_k)\to+\infty .
--   $$
--
--   This is the barrier property: the extension of $f_q$ by $+\infty$ outside $\mathcal D$ is closed.
--
--   Differences from the source:
--   - encoding: every sequence x_k ∈ 𝒟 with x_k → x_∞ ∈ ∂𝒟 has f_q(x_k) → +∞ → f_q tends to +∞ along the filter 𝓝[𝒟] x₀ at every frontier point x₀ of 𝒟; reason: in the metric space ℝᵐ the filter and sequential forms are equivalent
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.10, p.21

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_barrier

open Filter Topology

namespace MatrixLewis

/-- **Lemma 3.10** (Boundary blow-up; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), p.21). Let `x_k ∈ 𝒟` converge to a point `x_∞` of
the boundary of `𝒟`. Then `f_q(x_k) → +∞`.

**Formalization Note** Stated with filters: for every frontier point `x₀` of `𝒟`,
`f_q(x) → +∞` as `x → x₀` within `𝒟`; in the metric space `ℝᵐ` this is equivalent to the
sequential statement. Standing assumptions of §3 (symmetric `A₁, …, A_m, C`, Assumption 3.1,
real `q > 2`) are hypotheses. -/
theorem lemma_3_10 {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (h31 : Assumption31 A) (hq : 2 < q) :
    ∀ x₀ ∈ frontier (dom A C), Tendsto (barrier q A C) (𝓝[dom A C] x₀) atTop := by sorry

end MatrixLewis
