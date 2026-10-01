-- Prove2me | Theorems.Thm_Monod_not_isAmenableRel_mob
-- name    : Monod.not_isAmenableRel_mob
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T13:01:20.660885+00:00
-- url     : https://prove2.me/theorems/cd1593e7-7c27-45a0-9cd6-fb85fd82e011
-- title:
--   p. 2 (Carrière–Ghys) — the orbit relation of PSL₂(A) on P¹ is non-amenable
-- statement:
--   Let $A$ be a countable dense subring of $\mathbf{R}$. The equivalence relation on $\mathbf{P}^1$ induced by $\mathrm{PSL}_2(A)$, $x \sim y$ iff $g x = y$ for some $g \in \mathrm{SL}_2(A)$ acting by Möbius transformations, is not amenable (`IsAmenableRel`) for the Lebesgue measure class on $\mathbf{P}^1$ (`volP1`).
--
--   **Source.** Monod obtains this from Carrière–Ghys (*C. R. Acad. Sci. Paris* 1985, Théorème 3: the relation induced on $\mathrm{PSL}_2(\mathbf{R})$ by a countable dense subgroup is non-amenable), passed to $\mathbf{P}^1$ through Zimmer's amenable actions (Zimmer 1978, 1984; Adams–Elliott–Giordano 1994). $\mathrm{SL}_2(A)$ and $\mathrm{PSL}_2(A)$ have the same orbits, since $-1$ acts trivially.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 2, proof of Theorem 1

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem not_isAmenableRel_mob (A : Subring ℝ) [Countable A] (hA : Dense (A : Set ℝ)) :
    ¬ IsAmenableRel volP1
      {p : OnePoint ℝ × OnePoint ℝ | ∃ g : Matrix.SpecialLinearGroup (Fin 2) A, mob g p.1 = p.2} := by
  sorry

end Monod
