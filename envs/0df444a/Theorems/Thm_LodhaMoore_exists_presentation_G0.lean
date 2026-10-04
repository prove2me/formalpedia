-- Prove2me | Theorems.Thm_LodhaMoore_exists_presentation_G0
-- name    : LodhaMoore.exists_presentation_G0
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T08:24:14.758825+00:00
-- url     : https://prove2.me/theorems/f8a6da48-19c5-442b-b604-1475f0223c13
-- title:
--   §3 — G₀ has a presentation with three generators and nine relations
-- statement:
--   $G_0$ is presented by the generators $a$, $b$, $c$ and the nine relations `nineRels` (products left to right): the homomorphism from that presented group to the homeomorphisms of the projective line with products left to right, sending the generators to $a$, $b$, $c$, is injective with image $G_0$. The fourth and ninth relations are corrected (see the note on the definitions). The paper's "suffice" rests on Theorem 3.3 ($R_0$ presents $G_0$); the statement asserts the resulting presentation outright.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 7, §3

import Mathlib
import Definitions.Def_LodhaMoore

namespace LodhaMoore

theorem exists_presentation_G0 :
    ∃ phi : PresentedGroup nineRels →* (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ,
      phi (PresentedGroup.of .a) = MulOpposite.op a ∧ phi (PresentedGroup.of .b) = MulOpposite.op b ∧
      phi (PresentedGroup.of .c) = MulOpposite.op c ∧ Function.Injective phi ∧ phi.range = G0.op := by
  sorry

end LodhaMoore
