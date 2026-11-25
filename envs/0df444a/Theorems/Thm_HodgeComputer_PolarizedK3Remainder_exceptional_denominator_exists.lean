-- Prove2me | Theorems.Thm_HodgeComputer_PolarizedK3Remainder_exceptional_denominator_exists
-- name    : HodgeComputer.PolarizedK3Remainder.exceptional_denominator_exists
-- status  : Open
-- author  : @pageman
-- created : 2026-11-25T01:50:33.522131+00:00
-- url     : https://prove2.me/theorems/9738b5eb-a08d-58d2-91f1-9a9f10ac6d51
-- title:
--   Polarized K3 remainder: existence of an exceptional NormalChart denominator
-- statement:
--   For the polarized-k3-remainder instance, there exist some positive degree $e$, a nonzero homogeneous denominator $S$ of degree $e$ relatively prime to $F$, homogeneous numerators $W_j$ of degree $e+1$, and a quotient $Q$ satisfying $\operatorname{residue}_{F,A}(S,W)=FQ$. Any such $S$ must be exceptional: a generic homogeneous $S$ of degree $e$ makes the linear system for $W$ underdetermined-hostile relative to the residue conditions in the quotient by $(F)$. The statement records unrestricted-degree existence of an exceptional NormalChart witness.
-- source:
--   https://github.com/hodge-computer/sextics/blob/main/data/polarized-k3-remainder/why.md ; Diamond arXiv:2603.29157

import Definitions.Def_HodgeComputerPolarizedK3Remainder
import Definitions.Def_HodgeComputerNormalChart

set_option autoImplicit false
open HodgeComputer HodgeComputer.PolarizedK3Remainder

theorem HodgeComputer.PolarizedK3Remainder.exceptional_denominator_exists :
    ∃ (e : ℕ) (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      0 < e ∧ S ≠ 0 ∧ S.IsHomogeneous e ∧ IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (e + 1)) ∧
      NormalChart.residue F A S W = F * Q := by sorry
