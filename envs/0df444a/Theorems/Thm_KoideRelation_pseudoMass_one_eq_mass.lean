-- Prove2me | Theorems.Thm_KoideRelation_pseudoMass_one_eq_mass
-- name    : KoideRelation.pseudoMass_one_eq_mass
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T15:08:43.256521+00:00
-- url     : https://prove2.me/theorems/9362d224-fbe6-4f5c-a11d-203be35015b5
-- title:
--   Pseudo-masses reduce to physical masses at $U = \mathrm{Id}$ (eqs. 3.31-3.32)
-- statement:
--   The source's proposed extension of the relation to the neutrino and quark sectors replaces the physical masses by the **pseudo-masses** $\tilde m_i = \left|\sum_j (U_L)_{ij} m_j\right|$ built from the flavour mixing matrix, and asks for $\sum_i \tilde m_i = \tfrac23\left(\sum_i \sqrt{\tilde m_i}\right)^2$ (eqs. (3.31)–(3.32)). This milestone records the consistency requirement that makes (3.31) an extension rather than a different relation: for nonnegative masses and trivial mixing $U_L = \mathrm{Id}$, the pseudo-masses are the masses themselves,
--
--   $$ \tilde m = m, \qquad q(\tilde m) = q(m), $$
--
--   so (3.31) specializes to the original relation (3.1).
-- source:
--   Goffinet, François, "A bottom-up approach to fermion masses", PhD thesis, Université catholique de Louvain, December 2008, http://hdl.handle.net/2078.1/20873, Chapter 3 "A Mass Relation", p. 73, eqs. (3.31)-(3.32)

import Definitions.Def_KoideRelation_defs

namespace KoideRelation

theorem pseudoMass_one_eq_mass (m : Fin 3 → ℝ) (hm : ∀ i, 0 ≤ m i) :
    pseudoMass 1 m = m ∧ koideRatio (pseudoMass 1 m) = koideRatio m := by sorry

end KoideRelation
