-- Prove2me | Theorems.Thm_Grothendieck_Er_strictMono
-- name    : Grothendieck.Er_strictMono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T14:22:34.498591+00:00
-- url     : https://prove2.me/theorems/bed01e70-6b1d-4731-ae30-186c01e49c45
-- title:
--   $E_r$ is strictly increasing on $[0,1]$
-- statement:
--   For every integer $r\ge1$, if $0\le s<t\le1$ then
--
--   $$
--   E_r(s)<E_r(t).
--   $$
--
--   So $E_r$ is strictly increasing — hence injective — on $[0,1]$, and by oddness on $[-1,1]$. This is what makes the object of Section 3 well posed: the paper Taylor-expands the inverse function $E_r^{-1}$ and evaluates it at $t\,\beta(r,G)$ for $|t|\le1$, and it uses positivity of the coefficients and continuity to conclude that $\sum_k|b_{2k+1}|\beta^{2k+1}=1/(\vartheta(G)-1)$ has at most one solution. Strict monotonicity of $E_r$ underlies both readings.
--
--   The proof compares the difference series of $E_r(t)$ and $E_r(s)$ termwise: the coefficients $C_r(1/2)_k^2/((r/2+1)_k\,k!)$ are positive and $t^{2k+1}-s^{2k+1}>0$ for $t>s\ge0$, so the difference series has positive terms; it is summable at $t\le1$ because $\sum_k \mathrm{ErCoeff}_r(k)$ converges.
--
--   **Formalization Note** A supporting lemma rather than a verbatim statement of the paper: it supplies the invertibility on $[-1,1]$ that the paper's use of $E_r^{-1}$ presupposes.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib
import Definitions.Def_Grothendieck_Series

open MeasureTheory intervalIntegral
open scoped BigOperators Real

namespace Grothendieck

/-- **`E_r` is strictly increasing on `[0,1]`** (so injective there), which is what makes `E_r⁻¹`
of the paper's Section 3 the genuine inverse of `E_r` on the relevant range. -/
theorem Er_strictMono {r : ℕ} (hr : 1 ≤ r) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    Er r s < Er r t := by sorry

end Grothendieck
