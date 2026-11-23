-- Prove2me | Theorems.Thm_HodgeComputer_CycleQ2_normalChart_degree_at_least_two_witness
-- name    : HodgeComputer.CycleQ2.normalChart_degree_at_least_two_witness
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T20:25:24.385537+00:00
-- url     : https://prove2.me/theorems/9d6b8844-bf65-41ca-91c2-d58c37bc0f39
-- title:
--   Cycle q2: normal-chart residue witness of degree at least two
-- statement:
--   For exactly the sextic $F$ and source $A$ of the cycle-q2 instance, put $q=2$ and $B=A/q$. There exist complex polynomials $S,W_1,\ldots,W_5,Q$ with $S\ne 0$, $S$ homogeneous of degree $e=\deg S$, and
--
--   $$
--   2\le e,
--   $$
--
--   such that $\operatorname{IsRelPrime}(F,S)$, every $W_j$ is homogeneous of degree $e+7$, and
--
--   $$
--   \mathcal R_{F,B}(S,W)=F^q Q.
--   $$
--
--   The residue operator is unchanged from the positive-degree statement: $P=\partial_0 F$, $F_j=\partial_j F$, and
--
--   $$
--   \mathcal R_{F,B}(S,W)=S^2(PB_0-BP_0)+\sum_{j=1}^5\left[P^2 S\,\partial_j W_j-PSF_j\,\partial_0 W_j+\bigl(F_j(SP_0+PS_0)-P(SP_j+PS_j)\bigr)W_j\right].
--   $$
--
--   A witness of degree at least $2$ is a positive-degree witness. The linear locus was sampled and left a rank gap of one, including every weight-homogeneous line, the same-weight pencils, and the sum of all six variables.
--
--   **Formalization Note** The degree bound is `2 ≤ S.totalDegree`. The data $F$, $A$, and $\mathcal R$ are the platform definitions `HodgeComputer.CycleQ2` and `HodgeComputer.NormalChart`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/83fbf5c9a0afe9136ce4f1ed324d085a2c899bd0/data/cycle-q2/instance.rec; docs/01-certificates.md, normalized equations E1 and E2. Sufficient child of HodgeComputer.CycleQ2.normalChart_positive_degree_witness, https://prove2.me/theorems/a699465f-226c-481a-a463-dec519829f92, strengthening 1 ≤ deg S to 2 ≤ deg S.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.CycleQ2

theorem HodgeComputer.CycleQ2.normalChart_degree_at_least_two_witness :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      NormalChart.residue F (MvPolynomial.C ((2 : ℂ)⁻¹) * A) S W = F ^ 2 * Q := by sorry
