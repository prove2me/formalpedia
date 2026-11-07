-- Prove2me | Theorems.Thm_MatMulDS_corollary_7_2
-- name    : MatMulDS.corollary_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:05:25.003199+00:00
-- url     : https://prove2.me/theorems/da5b2777-2c01-4f92-a225-1c9bf7219590
-- title:
--   Corollary 7.2 — below the score $0.1900226$
-- statement:
--   Let $\mathbb F$ be a field of characteristic zero. For all constants $0<\kappa<0.1900226$ and $q_0>0$ there is a constant $\gamma>0$ such that arbitrary $A\in\mathbb F^{N\times D}$ and $B\in\mathbb F^{D\times N}$ with $D\le N^\kappa$ admit a deterministic bilinear data structure with preprocessing time and space
--   $$O(N^{2-\gamma})$$
--   and worst-case query time $O(N^{\kappa q_0})$ for adaptive queries, without using any bound on rectangular matrix multiplication.
--
--   This is the thin data structure that the lifting of Lemma 4.3 starts from.
--
--   Differences from the source:
--   - encoding: "preprocessing time and space", "adaptive" → the bound on $T_{\mathrm{pre}}$ of a uniform bilinear family; reason: the space of the evaluated structure is at most its preprocessing time, and a query's circuits depend only on that query (§4.1, p.16; p.46)
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Corollary 7.2, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_MatMulDS_UniformFamily

set_option autoImplicit false

namespace MatMulDS

/-- **Corollary 7.2 (Below the Score), p.45** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). For all constants
`0 < κ < 0.1900226` and `q0 > 0` there is a constant `γ > 0` such that arbitrary `A ∈ F^{N×D}` and `B ∈ F^{D×N}` with `D ≤ N^κ` admit a deterministic bilinear
data structure with preprocessing time and space `O(N^{2−γ})` and worst-case query time `O(N^{κ q0})` for adaptive queries.

**Formalization Note** `F` is a field of characteristic zero (§7, p.43). `O(·)` is `C ·` with `C` fixed before `N`, `D`. The conclusion mentions no bound on `ω`,
which is the clause "without using any bound on rectangular matrix multiplication". -/
theorem corollary_7_2 (F : Type) [Field F] [CharZero F] [DecidableEq F] (κ q0 : ℝ) (hκ : 0 < κ)
    (hκ' : κ < 0.1900226) (hq0 : 0 < q0) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
      AdmitsDS F (fun N Dm => 1 ≤ N ∧ 1 ≤ Dm ∧ (Dm : ℝ) ≤ (N : ℝ) ^ κ)
        (fun N _ => C * (N : ℝ) ^ (2 - γ)) (fun N _ => C * (N : ℝ) ^ (κ * q0)) := by sorry

end MatMulDS
