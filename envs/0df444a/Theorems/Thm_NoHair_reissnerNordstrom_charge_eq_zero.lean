-- Prove2me | Theorems.Thm_NoHair_reissnerNordstrom_charge_eq_zero
-- name    : NoHair.reissnerNordstrom_charge_eq_zero
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T20:34:38.376542+00:00
-- url     : https://prove2.me/theorems/1a9bd4ac-c8f6-4b2c-8600-749e1d8de850
-- title:
--   A vanishing duality-rotated Reissner–Nordström field forces zero charge
-- statement:
--   Let $m>0$ and $e^2\leq m^2$. Write $g$ and $F$ for the Reissner–Nordström metric and Maxwell field of mass $m$ and charge $e$, and $\star_g$ for its Hodge dual on two-forms. For any fixed real angle $\beta$, vanishing of the rotated field throughout the exterior forces
--
--   $$
--   \left.\big(\cos\beta\,F+\sin\beta\,\star_g F\big)\right|_{r>m+\sqrt{m^2-e^2}}=0
--   \quad\Longrightarrow\quad e=0.
--   $$
--
--   This identifies the vacuum members of the static charged family even when the exterior isometry specifies the Maxwell field only up to electromagnetic duality.
-- source:
--   T. Adamo and E. T. Newman, Kerr–Newman metric, §2.1, Eq. (2.8), p. 5, https://arxiv.org/abs/1410.6626. W. T. Emond et al., Amplitudes from Coulomb to Kerr–Taub–NUT, §1, Eqs. (1.1)–(1.3), p. 3, https://doi.org/10.1007/JHEP05(2022)055.

import Definitions.Def_NoHair_coordinates

theorem NoHair.reissnerNordstrom_charge_eq_zero (m e β : ℝ)
    (hp : NoHair.IsKerrNewmanBlackHoleParams m 0 e)
    (hzero : ∀ y ∈ NoHair.kerrNewmanDOC m 0 e,
      Real.cos β • NoHair.kerrNewmanField 0 e y +
        Real.sin β • NoHair.hodgeDual (NoHair.kerrNewmanMetric m 0 e y)
          (NoHair.kerrNewmanField 0 e y) = 0) :
    e = 0 := by sorry
