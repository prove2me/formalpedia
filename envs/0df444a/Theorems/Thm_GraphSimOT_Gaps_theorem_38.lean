-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_theorem_38
-- name    : GraphSimOT.Gaps.theorem_38
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:07:43.091044+00:00
-- url     : https://prove2.me/theorems/05d7bfe2-f6c3-40c0-813c-80e0e0bfd1b6
-- title:
--   Theorem 38 — multiplicative rounding: some permutation matrix P has ζ_P ≤ (1 + 4α)ζ_Q, α = C_thin ln(2n) ln ln(4n)
-- statement:
--   Let $G, H$ be graphs on $[n]$, $n\ge2$ (App. E.2), let $C_{thin}$ be the constant of Theorem 35 and $\alpha := C_{thin}\ln(2n)\ln\ln(4n)$. Then for every $Q\in\mathrm{DS}(n)$ there is a permutation matrix $P$ with
--   $$\zeta_P\ \le\ (1+4\alpha)\,\zeta_Q.$$
--
--   With $Q$ optimal ($\zeta_Q = \delta^{OT}_\square$) this gives $\delta_\square\le(1+4\alpha)\delta^{OT}_\square$, the multiplicative half of Theorem 11.
--
--   **Formalization Note.** "The constant of Theorem 35" is any $C_{thin}>0$ with the property Theorem 35 asserts (`IsThinConstant`); the statement is made for each such constant.
--
--   Differences from the source:
--   - encoding: indices in [n] = {1, …, n} → Fin n = {0, …, n − 1}; reason: relabelling of the index set; no instance changes
--   - encoding: C_thin, the constant of Theorem 35 → any Cthin with 0 < Cthin and IsThinConstant Cthin (the conclusion of theorem_35); reason: Theorem 35 asserts only that such a constant exists; the statement holds for each of them, so with theorem_35 it gives the paper's
--   - encoding: a permutation matrix P ∈ Perm(n) → π.permMatrix ℝ for π : Equiv.Perm (Fin n); reason: Perm(n) is exactly the set of these matrices
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 34, Theorem 38

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_CutRounding

namespace GraphSimOT.Gaps

/-- Theorem 38 (App. E.2, p. 34): let `C_thin` be the constant of Theorem 35 (any `C > 0` with
the property `IsThinConstant C`) and `α := C_thin ln(2n) ln ln(4n)`. Then for every `Q ∈ DS(n)`
there is a permutation matrix `P` with `ζ_P ≤ (1 + 4α) ζ_Q`. -/
theorem theorem_38 (Cthin : ℝ) (hC : 0 < Cthin) (hthin : IsThinConstant Cthin)
    {n : ℕ} (hn : 2 ≤ n) (G H : SimpleGraph (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q ∈ doublyStochastic ℝ (Fin n)) :
    ∃ π : Equiv.Perm (Fin n), zeta G H (π.permMatrix ℝ) ≤
      (1 + 4 * (Cthin * Real.log (2 * n) * Real.log (Real.log (4 * n)))) * zeta G H Q := by sorry

end GraphSimOT.Gaps
