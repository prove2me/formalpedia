-- Prove2me | Theorems.Thm_KoideRelation_tau_mass_prediction
-- name    : KoideRelation.tau_mass_prediction
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T14:56:42.887257+00:00
-- url     : https://prove2.me/theorems/b7847fff-8561-4350-a7eb-254eb86d8a4b
-- title:
--   The $\tau$ mass predicted by $q = \tfrac23$ (eq. 3.4)
-- statement:
--   Imposing $q^l = \tfrac23$ on the charged leptons, with the measured values $m_e = 0.510998910$ MeV and $m_\mu = 105.6583663$ MeV, and selecting the root compatible with the normal hierarchy $m_\tau > m_\mu$, determines the $\tau$ mass:
--
--   $$ m_\tau = 1776.968874\ \text{MeV}, $$
--
--   equation (3.4) of the source (quoted there as $1776.968874 \pm 0.000061$ MeV, the error coming from the experimental uncertainties on $m_e$ and $m_\mu$, which are not part of this statement). The milestone certifies the central value to within $10^{-6}$ MeV: the exact root is $1776.96887372560\ldots$, to be compared with the direct measurement $m_\tau = 1776.99 \pm 0.29$ MeV. Without the hierarchy hypothesis the relation admits a second, much smaller root near $3.3$ MeV.
-- source:
--   Goffinet, François, "A bottom-up approach to fermion masses", PhD thesis, Université catholique de Louvain, December 2008, http://hdl.handle.net/2078.1/20873, Chapter 3 "A Mass Relation", p. 61, eq. (3.4), with the input masses of eq. (3.2)

import Definitions.Def_KoideRelation_defs

namespace KoideRelation

theorem tau_mass_prediction (mtau : ℝ) (hbig : 105.6583663 < mtau)
    (hq : koideRatio ![0.510998910, 105.6583663, mtau] = 2 / 3) :
    |mtau - 1776.968874| < 0.000001 := by sorry

end KoideRelation
