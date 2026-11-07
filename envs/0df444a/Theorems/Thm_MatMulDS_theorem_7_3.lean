-- Prove2me | Theorems.Thm_MatMulDS_theorem_7_3
-- name    : MatMulDS.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:08:34.690585+00:00
-- url     : https://prove2.me/theorems/0e6c89ed-ebb3-4b71-847a-61d67325ded4
-- title:
--   Theorem 7.3 — at and beyond a smooth exponent
-- statement:
--   Let $\mathbb F$ be a field of characteristic zero and $0<\alpha<1$, and suppose $\omega(1,s,1)\le2+\rho(s)$ for all $s\ge0$, for a nonnegative function $\rho$ with $\rho(\alpha)=\rho'(\alpha)=0$. Then there are constants $\delta,\gamma>0$ such that arbitrary $A\in\mathbb F^{N\times D}$ and $B\in\mathbb F^{D\times N}$ with $D\le N^{\alpha+\delta}$ admit a deterministic bilinear data structure with preprocessing time and space
--   $$O(N^{2-\gamma})$$
--   and worst-case query time $O(N^{\alpha-\gamma})$ for adaptive queries. In particular, this holds for $D\le N^\alpha$, and then any $N^{2-\alpha}$ entries of $AB$, chosen adaptively, are computed in $O(N^{2-\gamma})$ time.
--
--   **Formalization Note** $\alpha$ is any value with these hypotheses, not necessarily the dual exponent.
--
--   Differences from the source:
--   - generalization: $\rho$ differentiable → $\rho$ differentiable at $\alpha$ only, nonnegative on $[0,\infty)$; reason: this makes the cited convexity [LR83] unnecessary for the goal; a differentiable $\rho$ is a special case
--   - encoding: "preprocessing time and space", "adaptive" → the bound on $T_{\mathrm{pre}}$ of a uniform bilinear family, and $T_{\mathrm{pre}}+MT_{\mathrm{query}}$ for $M\le N^{2-\alpha}$; reason: the space of the evaluated structure is at most its preprocessing time, and a query's circuits depend only on that query
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 7.3, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_MatMulDS_omegaExp
import Definitions.Def_MatMulDS_UniformFamily

set_option autoImplicit false

namespace MatMulDS

/-- **Theorem 7.3 (At and Beyond a Smooth Dual Exponent), p.46** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let `0 < α < 1`, and suppose `ω(1, s, 1) ≤ 2 + ρ(s)` for all `s ≥ 0`,
for a nonnegative function `ρ`, differentiable at `α`, with `ρ(α) = ρ′(α) = 0`. Then there are constants `δ, γ > 0` such that arbitrary `A ∈ F^{N×D}` and `B ∈ F^{D×N}` with `D ≤ N^{α+δ}` admit a deterministic bilinear data
structure with preprocessing time and space `O(N^{2−γ})` and worst-case query time `O(N^{α−γ})` for adaptive queries. In particular, this holds for `D ≤ N^α`, and then any `N^{2−α}` entries of `AB`, chosen adaptively, are
computed in `O(N^{2−γ})` time.

**Formalization Note.**
* `α` is any value with these hypotheses (footnote 9, p.46), not the dual exponent, and `F` is a field of characteristic zero (§7, p.43).
* `O(·)` is `C ·` with `C` fixed before `N`, `D`.
* The last clause counts preprocessing time plus `M ≤ N^{2−α}` query times; a query's circuits depend only on that query, so `M` queries chosen adaptively cost that much. -/
theorem theorem_7_3 (F : Type) [Field F] [CharZero F] [DecidableEq F] (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (ρ : ℝ → ℝ) (hρ0 : ∀ s, 0 ≤ s → 0 ≤ ρ s) (hρω : ∀ s, 0 ≤ s → omegaExp F 1 s 1 ≤ 2 + ρ s)
    (hρα : ρ α = 0) (hρ' : HasDerivAt ρ 0 α) :
    ∃ δ γ : ℝ, 0 < δ ∧ 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
      ∃ ds : ∀ x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ (x.2 : ℝ) ≤ (x.1 : ℝ) ^ (α + δ)},
          BilinearDS F x.1.1 x.1.2,
        UniformFamily (fun x : {x : ℕ × ℕ // 1 ≤ x.1 ∧ 1 ≤ x.2 ∧ (x.2 : ℝ) ≤ (x.1 : ℝ) ^ (α + δ)} => x.1.1)
          (fun x => x.1.2) ds (fun x => inputWords x.1.1 x.1.2) (fun x => Nat.clog 2 (x.1.1 + 1)) ∧
        (∀ x, ((ds x).Tpre : ℝ) ≤ C * (x.1.1 : ℝ) ^ (2 - γ) ∧
          ((ds x).Tquery : ℝ) ≤ C * (x.1.1 : ℝ) ^ (α - γ)) ∧
        ∀ x, (x.1.2 : ℝ) ≤ (x.1.1 : ℝ) ^ α → ∀ M : ℕ, (M : ℝ) ≤ (x.1.1 : ℝ) ^ (2 - α) →
          (((ds x).Tpre + M * (ds x).Tquery : ℕ) : ℝ) ≤ C * (x.1.1 : ℝ) ^ (2 - γ) := by sorry

end MatMulDS
