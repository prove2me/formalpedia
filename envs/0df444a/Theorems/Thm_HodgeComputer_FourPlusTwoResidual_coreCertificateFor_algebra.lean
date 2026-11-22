-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coreCertificateFor_algebra
-- name    : HodgeComputer.FourPlusTwoResidual.coreCertificateFor_algebra
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T13:53:30.219449+00:00
-- url     : https://prove2.me/theorems/c07e1cd3-2756-45dc-9bfe-a3bcd922a05c
-- title:
--   Bilinear product-denominator addition, degree promotion, and core-certificate equivalence for variable sources
-- statement:
--   Let $F_H(S, D, N) = 2 S D^2 - 2 D (N \cdot \nabla H) + 3 H (D \operatorname{div} N - N \cdot \nabla D)$ be the four-variable core residual of `four-plus-two-residual`. The predicate `CoreCertificateFor S D N` ($\deg D = d \ge 0$, $\deg N_i = d + 1$, $F_H(S, D, N) = 0$) satisfies three structural closure and bridge laws:
--
--   1. **Linear combination over unexpanded product denominators:** If `CoreCertificateFor S₁ D₁ N₁` and `CoreCertificateFor S₂ D₂ N₂` hold, then for any $c_1, c_2 \in \mathbb{C}$,
--
--   $$
--   \operatorname{CoreCertificateFor}\bigl(c_1 S_1 + c_2 S_2,\; D_1 D_2,\; c_1 D_2 N_1 + c_2 D_1 N_2\bigr)
--   $$
--
--   holds via $F_H(c_1 S_1 + c_2 S_2, D_1 D_2, c_1 D_2 N_1 + c_2 D_1 N_2) = c_1 D_2^2 F_H(S_1, D_1, N_1) + c_2 D_1^2 F_H(S_2, D_2, N_2)$.
--
--   2. **Denominator degree promotion:** Multiplying $(D, N)$ by any nonzero homogeneous polynomial $P$ of degree $m \ge 0$ preserves `CoreCertificateFor S` via $F_H(S, P D, P N) = P^2 F_H(S, D, N)$, reconciling $d = 0$ polynomial-exact remainders with $\deg D \ge 1$.
--
--   3. **Target equivalence:** `∃ D N, CoreCertificateFor coreSource D N` holds if and only if `∃ D N, CoreCertificate D N` holds.
-- source:
--   Hodge.computer Atlas Chapter 1 & instance `four-plus-two-residual`, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoSourceAlgebra

theorem HodgeComputer.FourPlusTwoResidual.coreCertificateFor_algebra :
    (∀ (c₁ c₂ : ℂ) (S₁ S₂ D₁ D₂ : MvPolynomial (Fin 4) ℂ)
      (N₁ N₂ : Fin 4 → MvPolynomial (Fin 4) ℂ),
      HodgeComputer.FourPlusTwoResidual.CoreCertificateFor S₁ D₁ N₁ →
      HodgeComputer.FourPlusTwoResidual.CoreCertificateFor S₂ D₂ N₂ →
      HodgeComputer.FourPlusTwoResidual.CoreCertificateFor
        (MvPolynomial.C c₁ * S₁ + MvPolynomial.C c₂ * S₂)
        (D₁ * D₂)
        (fun i => MvPolynomial.C c₁ * D₂ * N₁ i + MvPolynomial.C c₂ * D₁ * N₂ i)) ∧
    (∀ (m : ℕ) (P S D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
      P ≠ 0 → P.IsHomogeneous m →
      HodgeComputer.FourPlusTwoResidual.CoreCertificateFor S D N →
      HodgeComputer.FourPlusTwoResidual.CoreCertificateFor S (P * D) (fun i => P * N i)) ∧
    ((∃ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
        HodgeComputer.FourPlusTwoResidual.CoreCertificateFor
          HodgeComputer.FourPlusTwoResidual.coreSource D N) ↔
      (∃ (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ),
        HodgeComputer.FourPlusTwoResidual.CoreCertificate D N)) := by sorry
