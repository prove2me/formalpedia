-- Prove2me | Theorems.Thm_KoideRelation_koide_iff_sum_z_eq_zero
-- name    : KoideRelation.koide_iff_sum_z_eq_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T14:55:22.914705+00:00
-- url     : https://prove2.me/theorems/633860d8-c740-4607-87f7-dad0970bfd63
-- title:
--   Composite-model parametrization: Koide $\iff \sum_i z_i = 0$ (eqs. 3.18-3.22)
-- statement:
--   In the composite (preon) model discussed by the source, the charged-lepton masses take the form $m_i = E\,(z_i + z_0)^2$ with a common scale $E$ and a democratic component $z_0 = 1/\sqrt3$, the $z_i$ being normalized by $\sum_i z_i^2 = 1$ so that $Z = (z_1,z_2,z_3)$ is a unit vector in generation space (eqs. (3.18), (3.21), (3.22)). Under these conventions, and assuming the masses do not all vanish, Koide's relation is equivalent to the vanishing of the sum of the $z_i$:
--
--   $$ q(m) = \frac{2}{3} \iff \sum_i z_i = 0, $$
--
--   i.e. to $Z \perp Z_0 = (z_0,z_0,z_0)$ — equation (3.19), which the source compares with an anomaly-cancellation condition. The hypothesis that some mass is nonzero is what excludes the degenerate second root $\sum_i z_i = -\sqrt3$, where every $z_i = -1/\sqrt3$ and all masses vanish.
-- source:
--   Goffinet, François, "A bottom-up approach to fermion masses", PhD thesis, Université catholique de Louvain, December 2008, http://hdl.handle.net/2078.1/20873, Chapter 3 "A Mass Relation", pp. 68-69, eqs. (3.18)-(3.22) (with the normalization $\sum_i z_i^2 = 1$, $z_0 = 1/\sqrt3$)

import Definitions.Def_KoideRelation_defs

namespace KoideRelation

theorem koide_iff_sum_z_eq_zero (E : ℝ) (hE : 0 < E) (z : Fin 3 → ℝ)
    (hz : ∑ i, z i ^ 2 = 1) (hnn : ∀ i, 0 ≤ z i + 1 / Real.sqrt 3)
    (m : Fin 3 → ℝ) (hm : ∀ i, m i = E * (z i + 1 / Real.sqrt 3) ^ 2)
    (hne : ∃ i, m i ≠ 0) :
    koideRatio m = 2 / 3 ↔ ∑ i, z i = 0 := by sorry

end KoideRelation
