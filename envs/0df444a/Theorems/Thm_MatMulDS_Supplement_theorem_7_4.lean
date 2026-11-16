-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_7_4
-- name    : MatMulDS.Supplement.theorem_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:16:12.415204+00:00
-- url     : https://prove2.me/theorems/571d0b23-528f-432b-9af2-cf8df2fd4b36
-- title:
--   Theorem 7.4 — the square root: $D\le\lceil\sqrt N\rceil$ with $O(N^{1.9997334})$ preprocessing and $O(N^{0.4997334})$ queries; $\beta=0.0002666$ is admissible
-- statement:
--   Let $\mathbb F$ be a field of characteristic zero. Arbitrary $A\in\mathbb F^{N\times D}$ and $B\in\mathbb F^{D\times N}$ with $D\le\lceil\sqrt N\rceil$ admit a deterministic bilinear data structure with preprocessing time and space $O(N^{1.9997334})$ and worst-case query time $O(N^{0.4997334})$ for adaptive queries. In particular, any $N^{3/2}$ entries of $AB$, chosen adaptively, are computed in $O(N^{1.9997334})$ time. Together with Lemma 7.7 and Corollary 7.8, this shows that $\beta=0.0002666$ is an admissible saving (Definition 8.1).
--
--   This is the first explicit polynomial saving at the square root, and it is the admissible saving behind all numerical exponents of Section 8.
--
--   Differences from the source:
--   - encoding: "a deterministic bilinear data structure" for arbitrary $A,B$ → one uniform family of bilinear data structures (`UniformFamily`, `BilinearDS`) over all admissible $N,D\ge1$, $\mathbb F$ of characteristic zero fixed first; reason: as in the published Theorem 7.3; a bilinear data structure gives the deterministic one with space at most its preprocessing time and adaptive queries
--   - encoding: "any $M$ entries, chosen adaptively" → preprocessing time plus $M$ query times, for every admissible $M$; reason: a query's circuits depend only on that query, so adaptive choices cost the same
--   - encoding: $O(\cdot)$ → $C\cdot$ with $C$ fixed before the sizes, inside a ceiling as a step budget; reason: the meaning of $O$ for one fixed algorithm
--   - encoding: "Together with Lemma 7.7 and Corollary 7.8, this shows that $\beta=0.0002666$ is an admissible saving" → the conjunct `AdmissibleSaving 0.0002666`; reason: the printed last sentence of the theorem is a claim; Lemma 7.7 and Corollary 7.8 are its proof
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 7.4, p.47 (PDF p.49)

import Mathlib
import Definitions.Def_MatMulDS_UniformFamily
import Definitions.Def_MatMulDS_Supplement_AdmissibleSaving

set_option autoImplicit false

open MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem 7.4 (The Square Root), p.47** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256
6c5a1c16…). Arbitrary `A ∈ F^{N×D}` and `B ∈ F^{D×N}` with `D ≤ ⌈√N⌉` admit a deterministic bilinear data structure with
preprocessing time and space `O(N^{1.9997334})` and worst-case query time `O(N^{0.4997334})` for adaptive queries. In particular,
any `N^{3/2}` entries of `AB`, chosen adaptively, are computed in `O(N^{1.9997334})` time. Together with Lemma 7.7 and
Corollary 7.8, this shows that `β = 0.0002666` is an admissible saving (Definition 8.1).

**Formalization Note.**
* `F` is a field of characteristic zero (§7, p.43). `O(·)` is `C ·` with `C` fixed before `N`, `D`.
* The bilinear data structures form one uniform family `ds` over all `N, D ≥ 1` with `D ≤ ⌈√N⌉` (as in the published
  Theorem 7.3); a bilinear data structure gives the deterministic one, with space at most its preprocessing time, and its
  queries may be adaptive.
* "Any `N^{3/2}` entries" is: preprocessing time plus `M` query times, for every `M ≤ N^{3/2}`.
* The last sentence is stated as the conjunct `AdmissibleSaving 0.0002666`. -/
theorem theorem_7_4 (F : Type) [Field F] [CharZero F] [DecidableEq F] :
    (∃ C : ℝ, 0 < C ∧
      ∃ ds : ∀ x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ x.2 ≤ ⌈Real.sqrt x.1⌉₊}, BilinearDS F x.1.1 x.1.2,
        UniformFamily (fun x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ x.2 ≤ ⌈Real.sqrt x.1⌉₊} => x.1.1)
          (fun x => x.1.2) ds (fun x => inputWords x.1.1 x.1.2) (fun x => Nat.clog 2 (x.1.1 + 1)) ∧
        (∀ x, ((ds x).Tpre : ℝ) ≤ C * (x.1.1 : ℝ) ^ (1.9997334 : ℝ) ∧
          ((ds x).Tquery : ℝ) ≤ C * (x.1.1 : ℝ) ^ (0.4997334 : ℝ)) ∧
        ∀ x, ∀ M : ℕ, (M : ℝ) ≤ (x.1.1 : ℝ) ^ ((3 : ℝ) / 2) →
          (((ds x).Tpre + M * (ds x).Tquery : ℕ) : ℝ) ≤ C * (x.1.1 : ℝ) ^ (1.9997334 : ℝ)) ∧
    AdmissibleSaving 0.0002666 := by sorry

end MatMulDS.Supplement
