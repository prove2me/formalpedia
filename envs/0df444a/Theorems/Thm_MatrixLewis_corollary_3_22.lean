-- Prove2me | Theorems.Thm_MatrixLewis_corollary_3_22
-- name    : MatrixLewis.corollary_3_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:54.875464+00:00
-- url     : https://prove2.me/theorems/81717d47-848e-4437-9b4b-80b545bc7667
-- title:
--   Corollary 3.22 — self-concordance constant $C'_{\mathrm{sc}}q$ for $q\ge\log n$
-- statement:
--   There is an absolute constant $C'_{\mathrm{sc}}$ such that the following holds. Let $A_1,\dots,A_m,C\in\mathbb S^n$ with the $A_i$ satisfying Assumption 3.1, and let $q>2$ with $q\ge\log n$. At every strictly feasible $x\in\mathcal D$ and for all $h\in\mathbb R^m$,
--   $$
--   \bigl|D^3f_q(x)[h,h,h]\bigr|\le2K_q\bigl(D^2f_q(x)[h,h]\bigr)^{3/2},\qquad K_q:=C'_{\mathrm{sc}}q .
--   $$
--
--   Differences from the source:
--   - encoding: an absolute constant C′_sc → ∃ C′_sc > 0 quantified before all data; reason: a larger constant also works, so positivity is no restriction; log is natural
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Corollary 3.22, p.34, eq. (45)

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_barrier

namespace MatrixLewis

/-- **Corollary 3.22** (The constant for `q ≥ log n`; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), p.34, eq. (45)). Assume that
Assumption 3.1 holds, and let `q > 2` with `q ≥ log n`. For an absolute constant `C′_sc`, at every
strictly feasible `x` and for all `h ∈ ℝᵐ`, `|D³f_q(x)[h, h, h]| ≤ 2K_q(D²f_q(x)[h, h])^{3/2}`,
`K_q := C′_sc q`.

**Formalization Note** `C′_sc` is quantified before all data, and taken positive (any larger
constant also works, so this is no restriction). `log` is natural. The data are symmetric. -/
theorem corollary_3_22 :
    ∃ C'sc : ℝ, 0 < C'sc ∧
      ∀ (n m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (q : ℝ),
        (∀ i, (A i).IsHermitian) → C.IsHermitian → Assumption31 A → 2 < q →
        Real.log n ≤ q →
        ∀ x ∈ dom A C, ∀ h : EuclideanSpace ℝ (Fin m),
          |iteratedFDeriv ℝ 3 (barrier q A C) x (fun _ => h)| ≤
            2 * (C'sc * q) *
              (iteratedFDeriv ℝ 2 (barrier q A C) x (fun _ => h)) ^ ((3 : ℝ) / 2) := by sorry

end MatrixLewis
