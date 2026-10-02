-- Prove2me | Theorems.Thm_MooreFoelner_isMarginal_not_extended_Rf
-- name    : MooreFoelner.isMarginal_not_extended_Rf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T00:36:29.637661+00:00
-- url     : https://prove2.me/theorems/73852f2e-3e40-45f0-b29d-3e6be2fa9812
-- title:
--   Lemma 4.1 — the elements whose range tree misses a given sequence form a marginal set
-- statement:
--   For every finite binary sequence $u$, the set of $f$ in Moore's $F$ such that no element of $R_f$ extends $u$ is marginal for the right action of $F$ on itself.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 10, Lemma 4.1

import Mathlib
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem isMarginal_not_extended_Rf (u : Seq) :
    IsMarginal (rightMul : MooreF → MooreF → Option MooreF)
      {f | ¬ ∃ r ∈ Rf (toMap f), u <+: r} := by
  sorry

end MooreFoelner
