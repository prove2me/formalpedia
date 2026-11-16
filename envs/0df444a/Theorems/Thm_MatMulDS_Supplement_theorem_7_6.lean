-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_7_6
-- name    : MatMulDS.Supplement.theorem_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:17:45.956734+00:00
-- url     : https://prove2.me/theorems/9f448e9b-b8e0-476b-9ac1-3b946a5a5736
-- title:
--   Theorem 7.6 — every inner dimension up to $N^{\delta_*}$
-- statement:
--   Let $\mathbb F$ be a field of characteristic zero. For every fixed $0<\delta<\delta_*$ there is a constant $\gamma>0$ such that arbitrary $A\in\mathbb F^{N\times D}$ and $B\in\mathbb F^{D\times N}$ with $D\le N^\delta$ admit a deterministic bilinear data structure with preprocessing time and space $O(N^{2-\gamma})$ which returns any entry of $AB$, chosen adaptively, in $O(N^{\delta-\gamma})$ time. Consequently, any $M\le N^{2-\delta+\gamma/2}$ prescribed entries of $AB$ are computed in $O(N^{2-\gamma/2})$ time.
--
--   The bound of Proposition 4.5 on rectangular matrix multiplication is only used for $\delta\ge0.1900226$. The theorem covers every inner dimension below $N^{0.5012}$ with one statement.
--
--   Differences from the source:
--   - encoding: "a deterministic bilinear data structure" for arbitrary $A,B$ → one uniform family of bilinear data structures (`UniformFamily`, `BilinearDS`) over all admissible $N,D\ge1$, $\mathbb F$ of characteristic zero fixed first; reason: as in the published Theorem 7.3; a bilinear data structure gives the deterministic one with space at most its preprocessing time and adaptive queries
--   - encoding: "any $M$ entries, chosen adaptively" → preprocessing time plus $M$ query times, for every admissible $M$; reason: a query's circuits depend only on that query, so adaptive choices cost the same
--   - encoding: $O(\cdot)$ → $C\cdot$ with $C$ fixed before the sizes, inside a ceiling as a step budget; reason: the meaning of $O$ for one fixed algorithm
--   - encoding: $\delta_*$ → `deltaStar`, the exact value of (7.4); reason: as in Theorem 7.5
--   - reading: "The bound of Proposition 4.5 … is only used for $\delta\ge0.1900226$" → no hypothesis on $\omega$ for any $\delta$; reason: a remark on the proof; the cited bound is a theorem, not an assumption
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 7.6, p.48 (PDF p.50)

import Mathlib
import Definitions.Def_MatMulDS_UniformFamily
import Definitions.Def_MatMulDS_Supplement_deltaStar

set_option autoImplicit false

open MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem 7.6 (Every Inner Dimension up to N^{0.5012}), p.48** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission,
held file sha256 6c5a1c16…). For every fixed `0 < δ < δ_*` there is a constant `γ > 0` such that arbitrary `A ∈ F^{N×D}` and
`B ∈ F^{D×N}` with `D ≤ N^δ` admit a deterministic bilinear data structure with preprocessing time and space `O(N^{2−γ})` which
returns any entry of `AB`, chosen adaptively, in `O(N^{δ−γ})` time. Consequently, any `M ≤ N^{2−δ+γ/2}` prescribed entries of `AB`
are computed in `O(N^{2−γ/2})` time. The bound of Proposition 4.5 on rectangular matrix multiplication is only used for
`δ ≥ 0.1900226`.

**Formalization Note.**
* `δ_*` is `deltaStar`, the exact value of (7.4). `F` is a field of characteristic zero; `O(·)` is `C ·` with `C` fixed before
  `N`, `D`; the data structures form one uniform family over all `N, D ≥ 1` with `D ≤ N^δ`.
* The last sentence is a remark on the proof: the statement has no hypothesis on `ω`, the cited bound being a theorem. -/
theorem theorem_7_6 (F : Type) [Field F] [CharZero F] [DecidableEq F] :
    ∀ δ : ℝ, 0 < δ → δ < deltaStar →
      ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
        ∃ ds : ∀ x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ (x.2 : ℝ) ≤ (x.1 : ℝ) ^ δ}, BilinearDS F x.1.1 x.1.2,
          UniformFamily (fun x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ (x.2 : ℝ) ≤ (x.1 : ℝ) ^ δ} => x.1.1)
            (fun x => x.1.2) ds (fun x => inputWords x.1.1 x.1.2) (fun x => Nat.clog 2 (x.1.1 + 1)) ∧
          (∀ x, ((ds x).Tpre : ℝ) ≤ C * (x.1.1 : ℝ) ^ (2 - γ) ∧
            ((ds x).Tquery : ℝ) ≤ C * (x.1.1 : ℝ) ^ (δ - γ)) ∧
          ∀ x, ∀ M : ℕ, (M : ℝ) ≤ (x.1.1 : ℝ) ^ (2 - δ + γ / 2) →
            (((ds x).Tpre + M * (ds x).Tquery : ℕ) : ℝ) ≤ C * (x.1.1 : ℝ) ^ (2 - γ / 2) := by sorry

end MatMulDS.Supplement
