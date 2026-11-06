-- Prove2me | Theorems.Thm_MatrixLewis_theorem_3_21
-- name    : MatrixLewis.theorem_3_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:26.795576+00:00
-- url     : https://prove2.me/theorems/f955a473-d4cb-40bb-8b88-b96859e83b7b
-- title:
--   Theorem 3.21 — $f_q$ is self-concordant with constant $C_{\mathrm{sc}}q(1+\sqrt\beta)$ for every real $q>2$
-- statement:
--   There is an absolute constant $C_{\mathrm{sc}}\ge1$ such that the following holds. Let $A_1,\dots,A_m,C\in\mathbb S^n$ with the $A_i$ satisfying Assumption 3.1, let $q>2$ be real, and put $\beta=2n^{2/(q+2)}$. For every strictly feasible $x\in\mathcal D$ and every $h\in\mathbb R^m$,
--   $$
--   \bigl|D^3f_q(x)[h,h,h]\bigr|\le C_{\mathrm{sc}}\,q\,(1+\sqrt\beta)\,\bigl(D^2f_q(x)[h,h]\bigr)^{3/2}.
--   $$
--
--   Hence $f_q$ is self-concordant with constant $K_{q,n}:=C_{\mathrm{sc}}q(1+\sqrt\beta)=O(qn^{1/(q+2)})$.
--
--   Differences from the source:
--   - encoding: Dᵏf_q(x)[h,…,h] → iteratedFDeriv ℝ k f_q x (fun _ => h); reason: Fréchet derivatives on ℝᵐ
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Theorem 3.21, p.34, eq. (44)

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_barrier

namespace MatrixLewis

/-- **Theorem 3.21** (Self-concordance for every real `q > 2`; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), p.34, eq. (44)). Assume
that Assumption 3.1 holds, let `q > 2` be real, and put `β = 2n^{2/(q+2)}`, where `n` is the order
of the slack matrices. There is an absolute constant `C_sc ≥ 1` such that for every strictly
feasible `x` and every `h ∈ ℝᵐ`, `|D³f_q(x)[h, h, h]| ≤ C_sc q(1 + √β)(D²f_q(x)[h, h])^{3/2}`.

**Formalization Note** `C_sc` is quantified before `n`, `m`, the data and `q`. `Dᵏf_q(x)[h, …, h]`
is `iteratedFDeriv ℝ k f_q x (fun _ => h)`; strictly feasible means `x ∈ 𝒟`. The data
`A₁, …, A_m, C` are symmetric. -/
theorem theorem_3_21 :
    ∃ Csc : ℝ, 1 ≤ Csc ∧
      ∀ (n m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (q : ℝ),
        (∀ i, (A i).IsHermitian) → C.IsHermitian → Assumption31 A → 2 < q →
        ∀ x ∈ dom A C, ∀ h : EuclideanSpace ℝ (Fin m),
          |iteratedFDeriv ℝ 3 (barrier q A C) x (fun _ => h)| ≤
            Csc * q * (1 + Real.sqrt (2 * (n : ℝ) ^ (2 / (q + 2)))) *
              (iteratedFDeriv ℝ 2 (barrier q A C) x (fun _ => h)) ^ ((3 : ℝ) / 2) := by sorry

end MatrixLewis
