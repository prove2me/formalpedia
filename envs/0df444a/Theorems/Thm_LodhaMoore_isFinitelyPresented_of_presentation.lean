-- Prove2me | Theorems.Thm_LodhaMoore_isFinitelyPresented_of_presentation
-- name    : LodhaMoore.isFinitelyPresented_of_presentation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T08:07:45.352897+00:00
-- url     : https://prove2.me/theorems/13970141-0020-41eb-a23a-457ba509db43
-- title:
--   §3 — if R presents G and R₀ presents G₀, then both are finitely presented
-- statement:
--   If the generators $S$ and relations $R$ present $G$ (the homomorphism sending each generator to its function is injective with image $G$), then $G$ is finitely presented; and if the generators $S_0$ and relations $R_0$ present `G0Seq`, then `G0Seq` is finitely presented.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), pp. 6–7, §3

import Mathlib
import Definitions.Def_LodhaMoore

namespace LodhaMoore

theorem isFinitelyPresented_of_presentation :
    ((∃ phi : PresentedGroup R →* SeqGroup, (∀ g, phi (PresentedGroup.of g) = g.val) ∧
      Function.Injective phi ∧ phi.range = G) → Group.IsFinitelyPresented G) ∧
    ((∃ phi : PresentedGroup R0S →* SeqGroup, (∀ g, phi (PresentedGroup.of g) = g.1.val) ∧
      Function.Injective phi ∧ phi.range = G0Seq) → Group.IsFinitelyPresented G0Seq) := by
  sorry

end LodhaMoore
