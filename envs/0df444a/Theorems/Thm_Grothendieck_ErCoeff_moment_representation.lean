-- Prove2me | Theorems.Thm_Grothendieck_ErCoeff_moment_representation
-- name    : Grothendieck.ErCoeff_moment_representation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T14:49:26.589176+00:00
-- url     : https://prove2.me/theorems/dbfab66b-cb99-41a2-870c-538272e880a4
-- title:
--   The Taylor coefficients of $E_r$ are moments of an explicit measure on $[0,1]$
-- statement:
--   Write $E_r(t)=\sum_{k\ge0}\mathrm{ErCoeff}_r(k)\,t^{2k+1}$ for the paper's series, with
--
--   $$
--   \mathrm{ErCoeff}_r(k)=C_r\,\frac{(1/2)_k(1/2)_k}{(r/2+1)_k\,k!},\qquad C_r=\frac2r\Big(\frac{\Gamma((r+1)/2)}{\Gamma(r/2)}\Big)^2 .
--   $$
--
--   For every integer $r\ge1$ there is a **probability measure $\mu$ on $[0,1]$** with
--
--   $$
--   \mathrm{ErCoeff}_r(k)=C_r\int_0^1 x^k\,d\mu(x)\qquad\text{for all } k\ge0,
--   $$
--
--   i.e. $\mathrm{ErCoeff}_r/C_r$ is the moment sequence of a probability measure supported on $[0,1]$.
--
--   The measure is explicit: $\mu$ is the image of the product of two Beta-type measures under $(u,v)\mapsto uv$, one with density $\frac{u^{-1/2}(1-u)^{(r-1)/2}}{B(1/2,(r+1)/2)}$ on $[0,1]$, the other the arcsine density $\frac{v^{-1/2}(1-v)^{-1/2}}{B(1/2,1/2)}$. The $k$-th moments of these densities are $(1/2)_k/(r/2+1)_k$ and $(1/2)_k/k!$, and the product measure therefore has moments $(1/2)_k(1/2)_k/((r/2+1)_k\,k!)$.
--
--   Its role is §3 of the paper: it is exactly the representation (3.9) that the paper obtains from Hausdorff's moment theorem for completely monotone sequences. The value of stating it this way is that the measure is *exhibited* rather than asserted: no Hausdorff theorem is needed anywhere, and the moment property is proved by the Beta integral.
--
--   **Formalization Note** `μ` is a genuine `Measure ℝ` with `IsProbabilityMeasure`, supported on `Icc 0 1`. A supporting lemma for Lemma 3.5, not a verbatim statement of the paper.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — equation (3.9), p. 90 (via Hausdorff's moment theorem).

import Mathlib
import Definitions.Def_Grothendieck_Series

open MeasureTheory
open scoped BigOperators ENNReal

namespace Grothendieck

/-- **The Taylor coefficients of `E_r` are moments.** There is a probability measure `μ` on
`[0,1]` whose `k`-th moment is `ErCoeff r k / Cr r`; equivalently `ErCoeff r k = Cr r * ∫ x^k ∂μ`,
which is equation (3.9) of the paper. -/
theorem ErCoeff_moment_representation (r : ℕ) (hr : 1 ≤ r) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ k : ℕ, ErCoeff r k = Cr r * ∫ x, x ^ k ∂μ := by sorry

end Grothendieck
