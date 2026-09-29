-- Prove2me | Theorems.Thm_KeatingSnaith_cue_even_moment_asymptotics
-- name    : KeatingSnaith.cue_even_moment_asymptotics
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T12:54:09.299581+00:00
-- url     : https://prove2.me/theorems/c54fc44a-2c47-4618-a2a8-afdaf828a183
-- title:
--   $\langle|Z|^{2k}\rangle_{CUE}\sim\bigl(\prod_{j=0}^{k-1}\frac{j!}{(k+j)!}\bigr)N^{k^2}$
-- statement:
--   The **leading-order growth** of the even moments in the large-matrix limit.
--
--   Let $k$ be a non-negative integer. Then
--
--   $$
--   \lim_{N\to\infty}\;\frac{\bigl\langle |Z|^{2k}\bigr\rangle_{\mathrm{CUE}(N)}}{N^{k^{2}}} \;=\; \prod_{j=0}^{k-1}\frac{j!}{(k+j)!} .
--   $$
--
--   Equivalently, $\langle|Z|^{2k}\rangle = \bigl(\prod_{j=0}^{k-1} j!/(k+j)!\bigr)N^{k^2}+O(N^{k^2-1})$ as in the source.
--
--   The constant on the right is the random-matrix factor in the Keating–Snaith conjecture for the moments of the Riemann zeta function: it is the quantity conjectured to multiply the arithmetic factor in the asymptotics of $\frac1T\int_0^T|\zeta(1/2+it)|^{2k}\,dt$. In terms of the Barnes $G$-function it equals $G^2(1+k)/G(1+2k)$; it takes the values $1$ for $k=1$ and $1/12$ for $k=2$, matching the two classically known moments of $\zeta$.
-- source:
--   N. C. Snaith, Random Matrix Theory and zeta functions, PhD thesis, University of Bristol, June 2000, Chapter 2, p. 60, eq. (2.7.1), final line

import Definitions.Def_keating_snaith_cue

namespace KeatingSnaith

open Finset MeasureTheory Filter Topology
open scoped Real

/-- The leading order `N^{k²}` behaviour of `⟨|Z|^{2k}⟩` (thesis eq. (2.7.1)). -/
theorem cue_even_moment_asymptotics (k : ℕ) :
    Tendsto (fun N : ℕ => cueAverage N (fun θ => ‖charPoly N θ‖ ^ (2 * k)) / (N : ℝ) ^ (k ^ 2))
      atTop (𝓝 (∏ j ∈ Finset.range k,
        (Nat.factorial j : ℝ) / (Nat.factorial (k + j) : ℝ))) := by
  sorry

end KeatingSnaith
