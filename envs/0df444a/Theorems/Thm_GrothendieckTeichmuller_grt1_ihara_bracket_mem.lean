-- Prove2me | Theorems.Thm_GrothendieckTeichmuller_grt1_ihara_bracket_mem
-- name    : GrothendieckTeichmuller.grt1_ihara_bracket_mem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T21:42:59.231669+00:00
-- url     : https://prove2.me/theorems/495b1c2b-7cba-4502-acaa-3e2bbec66ce1
-- title:
--   Remark 7.1 — $\mathfrak{grt}_1$ is closed under the Ihara bracket
-- statement:
--   Let $\mathfrak{grt}_1 \subseteq \mathbb F(x,y)$ be the set of Lie polynomials satisfying the antisymmetry equation $\psi(y,x) = -\psi(x,y)$, the hexagon equation $\psi(x,y)+\psi(y,z)+\psi(z,x) = 0$ with $x+y+z=0$, and the pentagon equation in the Drinfeld-Kohno Lie algebra $\mathfrak t_4$.
--
--   If $f, g \in \mathfrak{grt}_1$ then their Ihara bracket $\{f,g\} = [f,g] + D_f g - D_g f$ again lies in $\mathfrak{grt}_1$.
--
--   Since $\mathfrak{grt}_1$ is a linear subspace by construction, this closure statement is exactly the assertion that $\mathfrak{grt}_1$ is a Lie subalgebra of the free Lie algebra equipped with the Ihara bracket - the Lie algebra structure of the graded Grothendieck-Teichmüller Lie algebra.
-- source:
--   Thomas Willwacher, The Grothendieck-Teichmüller Group, ETH Zürich lecture notes (in progress), 27 February 2014, Section 7.3, p. 55 (Lemma 7.2, Corollary 7.1, Remarks 7.1 and 7.2); Remark 4.4, p. 47

import Definitions.Def_GT_grt1

namespace GrothendieckTeichmuller

theorem grt1_ihara_bracket_mem (f g : Lxy) (hf : f ∈ grt1) (hg : g ∈ grt1) :
    iharaBracket f g ∈ grt1 := by sorry

end GrothendieckTeichmuller
