-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_no_low_degree_or_scalar_core_certificate
-- name    : HodgeComputer.FourPlusTwoResidual.no_low_degree_or_scalar_core_certificate
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T08:25:35.722979+00:00
-- url     : https://prove2.me/theorems/5d434242-0ae6-4eba-90f4-92543c2a60a0
-- title:
--   Nonexistence of scalar-core and low-degree core certificates on four-plus-two-residual
-- statement:
--   Let $H(x_0, x_1, y_0, y_1)$ be the sextic core of `four-plus-two-residual` and $A = x_0^3 y_0^3$. The space of four-variable core certificates satisfies three unconditional obstructions over $\mathbb{C}$:
--
--   1. **No scalar-multiple-of-core denominator:** For every $c \in \mathbb{C}$ and every $N$, $(c H, N)$ is not a `CoreCertificate`. Equivalently, the second-order pole equation $5 (N \cdot \nabla H) - 3 H \operatorname{div}(N) = 2 c A H$ has no polynomial solution $(c, N)$ with $c \neq 0$ (settling the $D = H$ case of Griffiths–Dwork reduction on $T_H$).
--
--   2. **Unconditional strictness at degree $6$:** Every homogeneous sextic denominator $D$ admitting a `CoreCertificate` satisfies $H \nmid D$ and therefore admits a `StrictCoreCertificate`.
--
--   3. **Low-degree exclusion ($\deg D \le 4$):** No homogeneous polynomial $D$ of degree $d \le 4$ admits a `CoreCertificate`.
--
--   **Formalization Note** Certified via exact integer Farkas dual functionals evaluated through a verified balanced merge engine over packed exponent keys.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` and GitHub Discussion #120 (`benediamond`, `kejace`, `DiamondJM`, `kmehltretter82`), https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoSymmetry

theorem HodgeComputer.FourPlusTwoResidual.no_low_degree_or_scalar_core_certificate :
    (∀ (c : ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      ¬ HodgeComputer.FourPlusTwoResidual.CoreCertificate
        (MvPolynomial.C c * HodgeComputer.FourPlusTwoResidual.core) N) ∧
    (∀ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      D.IsHomogeneous 6 →
      HodgeComputer.FourPlusTwoResidual.CoreCertificate D N →
      ¬ (HodgeComputer.FourPlusTwoResidual.core ∣ D) ∧
        ∃ p : Fin 4 → MvPolynomial (Fin 4) ℂ,
          HodgeComputer.FourPlusTwoResidual.StrictCoreCertificate D p) ∧
    (∀ (d : ℕ) (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      d ≤ 4 → D.IsHomogeneous d →
      ¬ HodgeComputer.FourPlusTwoResidual.CoreCertificate D N) := by sorry
