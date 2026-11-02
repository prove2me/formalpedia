-- Prove2me | Theorems.Thm_Grothendieck_cr_eq_norm_er_I
-- name    : Grothendieck.cr_eq_norm_er_I
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-02T04:17:01.810022+00:00
-- url     : https://prove2.me/theorems/63b548bf-7606-4883-8afa-3ecaa022f268
-- title:
--   Lemma 3.5 — $c_r = |E_r(i)|$
-- statement:
--   Let $r\ge2$ and let $c_r=\min\{|E_r(e^{it})|:t\in[0,2\pi]\}$. Then the minimum is attained at $t=\pi$:
--
--   $$
--   c_r=|E_r(i)|.
--   $$
--
--   The proof is the analytical counterpart of the previous lemma and is where the delicate sign analysis of the coefficient sequence sits. Writing $F_r(t)={}_2F_1(1/2,1/2;r/2+1;e^{it})$ and $|F_r(t)|^2=R_r(t)^2+I_r(t)^2$, one has $I_r(\pi)=0$ and $R_r(\pi+t)=R_r(\pi-t)$, so it suffices to show that $R_r$ is positive and decreasing on $(0,\pi)$. Positivity is Vietoris's theorem applied to the explicit coefficient sequence; monotonicity follows by writing those coefficients as the moments of a finite nonnegative measure (Hausdorff's theorem, applied to ratios of Gamma functions) and differentiating the imaginary part of the Poisson kernel.
--
--   **Formalization Note** The statement reads $c_r=\lVert E_r(i)\rVert$, where $E_r$ is the complex series `ErComplex r` evaluated at `Complex.I`; the hypothesis $2\le r$ is the paper's, and the case $r=1$ (where $c_1=0$) is not covered by the lemma.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, Lemma 3.5, p. 89. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib
import Definitions.Def_Grothendieck_Series

namespace Grothendieck

theorem cr_eq_norm_er_I (r : ℕ) (hr : 2 ≤ r) : cr r = ‖ErComplex r Complex.I‖ := by sorry

end Grothendieck
