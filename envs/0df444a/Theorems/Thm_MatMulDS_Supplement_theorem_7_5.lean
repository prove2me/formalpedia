-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_7_5
-- name    : MatMulDS.Supplement.theorem_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:17:17.438083+00:00
-- url     : https://prove2.me/theorems/2c5d5610-a468-4a3d-b26c-90529796e16c
-- title:
--   Theorem 7.5 — beyond the square root: every $1/2<\delta<\delta_*$
-- statement:
--   Let $\mathbb F$ be a field of characteristic zero and $\delta_*=0.5012157755649\ldots$ the value (7.4) for the second parameter set of Table 1. For every fixed $1/2<\delta<\delta_*$, in particular for every $1/2<\delta\le1/2+0.0012157$, there is a constant $\gamma>0$ such that arbitrary $A\in\mathbb F^{N\times D}$ and $B\in\mathbb F^{D\times N}$ with $D\le N^\delta$ admit a deterministic bilinear data structure with preprocessing time and space $O(N^{2-\gamma})$ and worst-case query time $O(N^{1/2-\gamma})$ for adaptive queries. In particular, any $N^{3/2}$ entries of $AB$, chosen adaptively, are computed in $O(N^{2-\gamma})$ time.
--
--   The theorem pushes the inner dimension of truly subquadratic data structures with sublinear queries past $\sqrt N$.
--
--   Differences from the source:
--   - encoding: "a deterministic bilinear data structure" for arbitrary $A,B$ → one uniform family of bilinear data structures (`UniformFamily`, `BilinearDS`) over all admissible $N,D\ge1$, $\mathbb F$ of characteristic zero fixed first; reason: as in the published Theorem 7.3; a bilinear data structure gives the deterministic one with space at most its preprocessing time and adaptive queries
--   - encoding: "any $M$ entries, chosen adaptively" → preprocessing time plus $M$ query times, for every admissible $M$; reason: a query's circuits depend only on that query, so adaptive choices cost the same
--   - encoding: $O(\cdot)$ → $C\cdot$ with $C$ fixed before the sizes, inside a ceiling as a step budget; reason: the meaning of $O$ for one fixed algorithm
--   - encoding: $\delta_*=0.5012157755649\ldots$ → `deltaStar`, the exact value of (7.4) from Table 1, set 2, with the closed forms (7.2); reason: the source defines $\delta_*$ by (7.4) "as above" and prints a truncation
--   - encoding: "in particular for every $1/2<\delta\le1/2+0.0012157$" → the conjunct $1/2+0.0012157<\delta_*$; reason: with the main clause it gives exactly the printed range
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 7.5, p.48 (PDF p.50); eq. (7.4) and Table 1, p.47

import Mathlib
import Definitions.Def_MatMulDS_UniformFamily
import Definitions.Def_MatMulDS_Supplement_deltaStar

set_option autoImplicit false

open MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem 7.5 (Beyond the Square Root), p.48** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256
6c5a1c16…). Let `δ_* = 0.5012157755649…` be as in (7.4). For every fixed `1/2 < δ < δ_*`, in particular for every
`1/2 < δ ≤ 1/2 + 0.0012157`, there is a constant `γ > 0` such that arbitrary `A ∈ F^{N×D}` and `B ∈ F^{D×N}` with `D ≤ N^δ` admit a
deterministic bilinear data structure with preprocessing time and space `O(N^{2−γ})` and worst-case query time `O(N^{1/2−γ})` for
adaptive queries. In particular, any `N^{3/2}` entries of `AB`, chosen adaptively, are computed in `O(N^{2−γ})` time.

**Formalization Note.**
* `δ_*` is `deltaStar`, the exact value of (7.4) for the second parameter set of Table 1. The "in particular" range is the conjunct
  `1/2 + 0.0012157 < δ_*`, which with the main clause gives every `1/2 < δ ≤ 1/2 + 0.0012157`.
* `F` is a field of characteristic zero; `O(·)` is `C ·` with `C` fixed before `N`, `D`; the data structures form one uniform family
  over all `N, D ≥ 1` with `D ≤ N^δ`. -/
theorem theorem_7_5 (F : Type) [Field F] [CharZero F] [DecidableEq F] :
    (1 : ℝ) / 2 + 0.0012157 < deltaStar ∧
    ∀ δ : ℝ, (1 : ℝ) / 2 < δ → δ < deltaStar →
      ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
        ∃ ds : ∀ x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ (x.2 : ℝ) ≤ (x.1 : ℝ) ^ δ}, BilinearDS F x.1.1 x.1.2,
          UniformFamily (fun x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ (x.2 : ℝ) ≤ (x.1 : ℝ) ^ δ} => x.1.1)
            (fun x => x.1.2) ds (fun x => inputWords x.1.1 x.1.2) (fun x => Nat.clog 2 (x.1.1 + 1)) ∧
          (∀ x, ((ds x).Tpre : ℝ) ≤ C * (x.1.1 : ℝ) ^ (2 - γ) ∧
            ((ds x).Tquery : ℝ) ≤ C * (x.1.1 : ℝ) ^ ((1 : ℝ) / 2 - γ)) ∧
          ∀ x, ∀ M : ℕ, (M : ℝ) ≤ (x.1.1 : ℝ) ^ ((3 : ℝ) / 2) →
            (((ds x).Tpre + M * (ds x).Tquery : ℕ) : ℝ) ≤ C * (x.1.1 : ℝ) ^ (2 - γ) := by sorry

end MatMulDS.Supplement
