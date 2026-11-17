-- Prove2me | Theorems.Thm_NewtonLCP_Supplement_theorem_7_17
-- name    : NewtonLCP.Supplement.theorem_7_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:21:15.594028+00:00
-- url     : https://prove2.me/theorems/5e8c395c-a7b2-4807-872f-e5d0f7c9f4e2
-- title:
--   Theorem 7.17 — Rump's theorem for $P_\star$-matrices via the inverse Cayley transform
-- statement:
--   Let $M\in\mathbb R^{n\times n}$. If $I_n+M$ is singular, then $M\notin P_0$. Suppose that $I_n+M$ is nonsingular, and let $\tilde M=C^{-1}(M)=(M-I_n)(M+I_n)^{-1}$. Then:
--
--   1. $M\in P$ if and only if $\rho^S_0(\tilde M)<1$.
--   2. $M\in P_\star\setminus P$ if and only if all of the following hold: $\rho^S_0(\tilde M)=1$; for all $x\in\mathbb R^n$, if $|\tilde Mx|\ge|x|$ then $|\tilde Mx|=|x|$; for all $x,y\in\mathbb R^n$, if $|\tilde Mx|=|x|$ and $\tilde Mx\circ\tilde My\ge x\circ y$ then $\tilde Mx\circ\tilde My=x\circ y$.
--   3. $M\in P_0$ if and only if $\rho^S_0(\tilde M)\le1$.
--
--   Here $|\cdot|$, $\ge$ and $\circ$ are entrywise, $P$ is the class of P-matrices, $P_\star$ the matrices of finite handicap and $P_0$ the matrices with nonnegative principal minors. The theorem gives a spectral characterization of $P$, $P_\star$ and $P_0$ in one statement.
--
--   **Formalization Note** $P$ is the published `PriceRobust.Stability.IsPMatrix`, $P_\star$ the published `IsPStar`, $P_0$ the published `IsP0`, $\rho^S_0$ the published `signRealSpecRad`; singularity is $\det(I_n+M)=0$.
--
--   Differences from the source: none.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 7.17, p.28 (proof p.28)

import Mathlib
import Definitions.Def_NewtonLCP_Rump
import Definitions.Def_NewtonLCP_MatrixClasses
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_PriceRobust_Stability_ZPMatrix
import Definitions.Def_NewtonLCP_Supplement_Cayley

open Matrix

namespace NewtonLCP.Supplement

/-- **Theorem 7.17** (Rump's theorem for `P⋆`-matrices). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 7.17, p.28 (proof p.28).

For `M ∈ ℝⁿˣⁿ`, if `Iₙ + M` is singular, then `M ∉ P₀`. Suppose that `Iₙ + M` is nonsingular,
and let `M̃ := C⁻¹(M) = (M − Iₙ)(M + Iₙ)⁻¹`. Then
(i) `M ∈ P` iff `ρ^S_0(M̃) < 1`;
(ii) `M ∈ P⋆ \ P` iff `ρ^S_0(M̃) = 1`; for all `x`, if `|M̃x| ≥ |x|` then `|M̃x| = |x|`; and for
all `x, y`, if `|M̃x| = |x|` and `M̃x ∘ M̃y ≥ x ∘ y` then `M̃x ∘ M̃y = x ∘ y`;
(iii) `M ∈ P₀` iff `ρ^S_0(M̃) ≤ 1`.

**Formalization Note.** `|·|`, `≥` and `∘` on vectors are entrywise. `P` is the published
`PriceRobust.Stability.IsPMatrix` (all nonempty principal minors positive), `P⋆` the published
`IsPStar` (finite handicap), `P₀` the published `IsP0`, `ρ^S_0` the published
`signRealSpecRad`, and `M̃` is `invCayley M`. "Singular" is `det = 0`. Every `n ≥ 0`. -/
theorem theorem_7_17 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    ((1 + M).det = 0 → ¬ IsP0 M) ∧
    ((1 + M).det ≠ 0 →
      (PriceRobust.Stability.IsPMatrix M ↔ signRealSpecRad (invCayley M) < 1) ∧
      (IsPStar M ∧ ¬ PriceRobust.Stability.IsPMatrix M ↔
        signRealSpecRad (invCayley M) = 1 ∧
        (∀ x : ι → ℝ, (∀ i, |x i| ≤ |(invCayley M *ᵥ x) i|) →
          ∀ i, |(invCayley M *ᵥ x) i| = |x i|) ∧
        (∀ x y : ι → ℝ, (∀ i, |(invCayley M *ᵥ x) i| = |x i|) →
          (∀ i, x i * y i ≤ (invCayley M *ᵥ x) i * (invCayley M *ᵥ y) i) →
          ∀ i, (invCayley M *ᵥ x) i * (invCayley M *ᵥ y) i = x i * y i)) ∧
      (IsP0 M ↔ signRealSpecRad (invCayley M) ≤ 1)) := by sorry

end NewtonLCP.Supplement
