-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_normalChart_residue_of_coreCertificate
-- name    : HodgeComputer.FourPlusTwoResidual.normalChart_residue_of_coreCertificate
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T08:25:35.389675+00:00
-- url     : https://prove2.me/theorems/5f8e0726-2721-43c9-a74a-c9e0e987f824
-- title:
--   Suspension bridge from a four-variable core certificate to normal-chart residue solvability
-- statement:
--   Let $F(X_0, X_1, X_2, Y_0, Y_1, Y_2) = H(X_0, X_1, Y_0, Y_1) + B(X_2, Y_2)$ and $A = X_0^3 Y_0^3$ be the protected six-variable sextic and source of `four-plus-two-residual`, where
--
--   $$
--   B(X_2, Y_2) = X_2^6 + \frac{15}{7} X_2^4 Y_2^2 + \frac{10}{7} X_2^2 Y_2^4 + Y_2^6.
--   $$
--
--   Given any four-variable `CoreCertificate` $(D, N)$ of homogeneous degrees $(k + 1, k + 2)$, setting $K = A D - N \cdot \nabla H$ and defining the six-variable denominator and tangential components
--
--   $$
--   S = 6 D H B, \qquad N^{(6)} = \bigl(6 H B N_0,\; 6 H B N_1,\; H K X_2,\; 6 H B N_2,\; 6 H B N_3,\; H K Y_2\bigr)
--   $$
--
--   with $W_j = N^{(6)}_{j+1}$ ($j \in \{0, \dots, 4\}$) yields a homogeneous normal-chart witness $(S, W, Q)$ of degrees $(k + 13, k + 14)$ with $\gcd(F, S) = 1$ satisfying
--
--   $$
--   \operatorname{NormalChart.residue}(F, A, S, W) = (\partial_{X_0} F)^2 \bigl(S \operatorname{div}(N^{(6)}) - N^{(6)} \cdot \nabla S\bigr) = F Q.
--   $$
--
--   **Formalization Note** Connects the normal-chart frontier leaf `normalChart_residue_solvable` directly to the four-variable core frontier leaf, unifying the two open decomposition branches of the mission.
-- source:
--   Hodge.computer Atlas Chapter 3B (Suspension / Thom–Sebastiani lift) and Prove2Me Mission `943587a6-8b99-482d-bd65-2c7c156ea445` (`xuanji`, `shivm`, `benediamond`, `kmehltretter82`)

import Definitions.Def_HodgeComputerFourPlusTwoResidual
import Definitions.Def_HodgeComputerFourPlusTwoCore
import Definitions.Def_HodgeComputerNormalChart
import Mathlib.RingTheory.Polynomial.UniqueFactorization

theorem HodgeComputer.FourPlusTwoResidual.normalChart_residue_of_coreCertificate
    (D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ)
    (h : HodgeComputer.FourPlusTwoResidual.CoreCertificate D N) :
    ∃ (S : HodgeComputer.AmbientPoly HodgeComputer.FourPlusTwoResidual.n)
      (W : Fin 5 → HodgeComputer.AmbientPoly HodgeComputer.FourPlusTwoResidual.n)
      (Q : HodgeComputer.AmbientPoly HodgeComputer.FourPlusTwoResidual.n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧
      IsRelPrime HodgeComputer.FourPlusTwoResidual.F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 1)) ∧
      HodgeComputer.NormalChart.residue
        HodgeComputer.FourPlusTwoResidual.F
        HodgeComputer.FourPlusTwoResidual.A S W =
        HodgeComputer.FourPlusTwoResidual.F * Q := by sorry
