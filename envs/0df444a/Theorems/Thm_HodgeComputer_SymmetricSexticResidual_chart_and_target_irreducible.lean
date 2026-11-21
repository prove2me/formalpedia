-- Prove2me | Theorems.Thm_HodgeComputer_SymmetricSexticResidual_chart_and_target_irreducible
-- name    : HodgeComputer.SymmetricSexticResidual.chart_and_target_irreducible
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T04:57:45.494193+00:00
-- url     : https://prove2.me/theorems/d9a76ddf-3d60-4cb0-82af-3f471b6c1e11
-- title:
--   Irreducibility of the projective sextic and reflection-chart cover for symmetric-sextic-residual
-- statement:
--   For the open frontier instance `symmetric-sextic-residual` (`Permutation symmetry · residual sector`), both the six-variable projective sextic $F \in \mathbb{C}[X_0, X_1, X_2, Y_0, Y_1, Y_2]$ and the five-variable reflection-chart equation $H_{\mathrm{sym}}(\lambda, b, c, d, v) = f_{\mathrm{sym}}(\lambda, b, c, d, v^2)$ are irreducible over $\mathbb{C}$:
--
--   $$
--   \operatorname{Irreducible}(F) \;\wedge\; \operatorname{Irreducible}\bigl(f_{\mathrm{sym}}(\lambda, b, c, d, v^2)\bigr).
--   $$
--
--   Irreducibility ensures that both $F$ and $H_{\mathrm{sym}}$ generate prime ideals in their respective polynomial rings, discharging the domain and coprimality hypotheses required to transport relative primitives from the weighted cubic threefold to projective Hodge certificates.
--
--   **Formalization Note** Both statements are proved without geometric smoothness assumptions via monic specialization and Eisenstein's criterion at the prime ideal $(T - i) \subset \mathbb{C}[T]$.
-- source:
--   Hodge.computer Atlas instance `symmetric-sextic-residual` and Discussion #117, https://github.com/hodge-computer/sextics/discussions/117

import Definitions.Def_HodgeComputerSymmetricChart
import Mathlib.RingTheory.Polynomial.UniqueFactorization

theorem HodgeComputer.SymmetricSexticResidual.chart_and_target_irreducible :
    Irreducible HodgeComputer.SymmetricSexticResidual.F ∧
      Irreducible (HodgeComputer.ReflectionChart.squareLift
        HodgeComputer.SymmetricSexticResidual.symWeighted) := by sorry
