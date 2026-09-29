-- Prove2me | Theorems.Thm_KoideRelation_koide_angle_eq_pi_div_four_iff
-- name    : KoideRelation.koide_angle_eq_pi_div_four_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T14:37:25.951359+00:00
-- url     : https://prove2.me/theorems/00731542-cf58-4d3f-8e1a-daf85d509dc9
-- title:
--   Koide's value $q = \tfrac23$ is exactly the $45^\circ$ cone (eqs. 3.5-3.6, Fig. 3.1)
-- statement:
--   For three nonnegative masses, not all zero, the vector of square-root masses $S = (\sqrt{m_1},\sqrt{m_2},\sqrt{m_3})$ makes an angle of exactly $45^\circ$ with the degeneracy direction $(1,1,1)$ if and only if Koide's relation holds:
--
--   $$ \psi = \frac{\pi}{4} \iff q(m) = \frac{2}{3}. $$
--
--   This is the content of Figure 3.1 and equations (3.5)–(3.6): the charged leptons place $S$ on the cone of aperture $\psi^l = (45.00005 \pm 0.00070)^\circ$ around $(1,1,1)$. Together with the previous milestone it says that Koide's relation is a purely geometric statement about the direction of $S$, invariant under the overall mass scale.
-- source:
--   Goffinet, François, "A bottom-up approach to fermion masses", PhD thesis, Université catholique de Louvain, December 2008, http://hdl.handle.net/2078.1/20873, Chapter 3 "A Mass Relation", pp. 62-63, eqs. (3.5)-(3.6) and Fig. 3.1

import Definitions.Def_KoideRelation_defs

namespace KoideRelation

theorem koide_angle_eq_pi_div_four_iff (m : Fin 3 → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hpos : ∃ i, 0 < m i) :
    koideAngle m = Real.pi / 4 ↔ koideRatio m = 2 / 3 := by sorry

end KoideRelation
