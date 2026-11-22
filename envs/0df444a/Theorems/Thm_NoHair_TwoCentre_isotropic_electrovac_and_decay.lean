-- Prove2me | Theorems.Thm_NoHair_TwoCentre_isotropic_electrovac_and_decay
-- name    : NoHair.TwoCentre.isotropic_electrovac_and_decay
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T21:44:55.941898+00:00
-- url     : https://prove2.me/theorems/4f53689b-31b8-4da5-8988-3877b29b410b
-- title:
--   The two-centre isotropic exterior satisfies Einstein–Maxwell with explicit asymptotic decay
-- statement:
--   On the punctured isotropic exterior, $U=1+|x+e_1|^{-1}+|x-e_1|^{-1}$, $g=-U^{-2}dt^2+U^2dx^2$, and $F=d(U^{-1}dt)$ solve all three coordinate Einstein–Maxwell equations of the no-hair mission. On $R=|x|>2$, every component satisfies the explicit end estimates
--
--   $$|g_{ij}-\eta_{ij}|\leq 64/R,\quad |\partial_k g_{ij}|\leq64/R^2,\quad |F_{ij}|\leq64/R^2.$$
--
--   The field equation assertion applies to every regular point in the original chart. The decay estimates share one constant in the exact coordinate conventions of the mission.
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696.

import Definitions.Def_NoHair_TwoCentreIsotropic

open NoHair NoHair.TwoCentre

theorem NoHair.TwoCentre.isotropic_electrovac_and_decay :
    (∀ y ∈ exterior, EinsteinMaxwellAt isotropicMetric field y) ∧
    (∀ y : E4, 2 < spatialRadius y → y ∈ exterior ∧ ∀ i j k,
      |isotropicMetric y i j - minkowski i j| ≤ 64 / spatialRadius y ∧
      |coordPartial (fun z => isotropicMetric z i j) k y| ≤ 64 / spatialRadius y ^ 2 ∧
      |field y i j| ≤ 64 / spatialRadius y ^ 2) := by
  sorry
