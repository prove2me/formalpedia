-- Prove2me | Theorems.Thm_Monod_mob_mem_orbit_H
-- name    : Monod.mob_mem_orbit_H
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T12:48:57.810819+00:00
-- url     : https://prove2.me/theorems/5c3ae7f4-f5ad-4b8a-b8a6-584df595e12e
-- title:
--   Proposition 9 — the orbits of PSL₂(A) and of H(A) agree on ℝ
-- statement:
--   Let $A$ be a subring of $\mathbf{R}$. (i) For every real $p$ and $g \in \mathrm{SL}_2(A)$, either $g \cdot p = \infty$ or $g \cdot p = h(p)$ for some $h \in H(A)$. (ii) For real $p, q$: $q = g \cdot p$ for some $g \in \mathrm{SL}_2(A)$ if and only if $q = h(p)$ for some $h \in H(A)$.
--
--   **Formalization Note.** (ii) is the source's second sentence: the two orbit equivalence relations coincide on $\mathbf{P}^1 \setminus \{\infty\}$.
-- source:
--   Monod, N., Groups of piecewise projective homeomorphisms, Proc. Natl. Acad. Sci. USA 110 (2013) 4524–4527, https://doi.org/10.1073/pnas.1218426110 (arXiv:1209.5229v2, whose page numbers are used), p. 2, Proposition 9

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective

namespace Monod

theorem mob_mem_orbit_H (A : Subring ℝ) :
    (∀ (p : ℝ) (g : Matrix.SpecialLinearGroup (Fin 2) A),
        mob g (p : OnePoint ℝ) = OnePoint.infty ∨ ∃ h ∈ H A, h (p : OnePoint ℝ) = mob g p) ∧
      ∀ p q : ℝ, (∃ g : Matrix.SpecialLinearGroup (Fin 2) A, mob g (p : OnePoint ℝ) = q) ↔
        ∃ h ∈ H A, h (p : OnePoint ℝ) = q := by
  sorry

end Monod
