-- Prove2me | Theorems.Thm_NewtonLCP_theorem_1_1
-- name    : NewtonLCP.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:28:48.038488+00:00
-- url     : https://prove2.me/theorems/64f86446-9aa0-4b85-aeeb-2a64f9ddf17c
-- title:
--   Theorem 1.1 — operator-norm characterization of $\mathcal P_\star$ and of $\hat\kappa(M)$
-- statement:
--   Let $M\in\mathbb R^{n\times n}$, $n\ge1$, and let $\mathcal D^n_{>0}$ be the set of positive diagonal matrices. Then $M\in\mathcal P_\star$ if and only if $I_n+DMD$ is nonsingular for every $D\in\mathcal D^n_{>0}$ and $\sup_{D\in\mathcal D^n_{>0}}\|(I_n+DMD)^{-1}\|_2$ is finite. If $M\in\mathcal P_\star$, then
--
--   $$\sup_{D\in\mathcal D^n_{>0}}\big\|(I_n+DMD)^{-1}\big\|_2=\sqrt{1+\frac{\hat\kappa(M)^2}{1/4+\hat\kappa(M)}}.\qquad(2)$$
--
--   Here $\|\cdot\|_2$ is the spectral ($\ell_2\to\ell_2$ operator) norm. Since the Newton matrix is $(I_n+\frac1\mu XMX)^{-1}$, the theorem bounds every Newton matrix by $\sqrt{1+\hat\kappa(M)}$; it also yields Väliaho's transposition theorem.
--
--   **Formalization Note** The supremum is stated as a least upper bound of the set of norms; finiteness is boundedness of that set.
--
--   Differences from the source:
--   - encoding: M ∈ ℝ^{n×n} for every n → [Nonempty ι] (n ≥ 1); reason: at n = 0 the printed operator norm max_{‖x‖₂=1} is a maximum over an empty set; the case is undefined
--   - encoding: sup is finite; sup equals (2) → BddAbove of the set of norms; IsLUB of that set at the value (2); reason: the real supremum of a set is stated through its least upper bound
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Theorem 1.1, p.3 (proof §9.1, pp.33–34)

import Mathlib
import Definitions.Def_NewtonLCP_Handicap

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NewtonLCP

/-- **Theorem 1.1** (operator-norm characterization of P⋆ and of the handicap number).
Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 1.1, p.3 (proof §9.1, pp.33–34).

Let `M ∈ ℝⁿˣⁿ`. Then `M ∈ P⋆` if and only if `Iₙ + DMD` is nonsingular for every positive
diagonal `D` and `sup_{D > 0} ‖(Iₙ + DMD)⁻¹‖₂` is finite. If `M ∈ P⋆`, then
`sup_{D > 0} ‖(Iₙ + DMD)⁻¹‖₂ = √(1 + κ̂(M)²/(1/4 + κ̂(M)))` (2).

**Formalization Note.** `D = diag(d)` with `d > 0`; `‖·‖` is the ℓ₂ → ℓ₂ operator norm
(`Matrix.Norms.L2Operator`). The supremum is stated with `BddAbove`/`IsLUB` over the set of
norms. `[Nonempty ι]` (n ≥ 1): at `n = 0` the printed `max_{‖x‖₂ = 1}` is over an empty set. -/
theorem theorem_1_1 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (M : Matrix ι ι ℝ) :
    (IsPStar M ↔
      (∀ d : ι → ℝ, (∀ i, 0 < d i) → (1 + diagonal d * M * diagonal d).det ≠ 0) ∧
      BddAbove {r : ℝ | ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧
        r = ‖(1 + diagonal d * M * diagonal d)⁻¹‖}) ∧
    (IsPStar M →
      IsLUB {r : ℝ | ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧ r = ‖(1 + diagonal d * M * diagonal d)⁻¹‖}
        (Real.sqrt (1 + handicap M ^ 2 / (1 / 4 + handicap M)))) := by sorry

end NewtonLCP
