-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_dyadic_potential_bound
-- name    : OAI.AsymptoticallyMinimalLittlewood.dyadic_potential_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:46:44.047963+00:00
-- url     : https://prove2.me/theorems/f4a4710b-f164-4fd5-9692-b4a5c1f31ecc
-- title:
--   Geometric decay of the scaled entropy potential $\sqrt{s\log(2R/s)}/2^{j}$ under the mass bound $s\le 2^{j}\mu$
-- statement:
--   Let $\mu$, $R$ and $s$ be real numbers with $\mu>0$, $2\mu\le R$ and $s\ge 0$, and let $j\ge 0$ be an integer. If $s\le 2^{j}\mu$, then
--
--   $$
--   \frac{\sqrt{s\log(2R/s)}}{2^{j}}\le\Bigl(\frac34\Bigr)^{j}\sqrt{\mu\log\frac{2R}{\mu}} .
--   $$
--
--   The expression $\sqrt{s\log(2R/s)}$ is the size of the square-root-logarithmic discrepancy bound for signing $s$ columns of a matrix with $R$ rows and entries in $[-1,1]$. In a dyadic rounding scheme of total mass at most $\mu$, at most $2^{j}\mu$ coordinates are active at scale $j$ and the signing error there is divided by $2^{j}$. The inequality says that these scale-$j$ contributions decay geometrically with ratio $3/4$; consequently their sum over all scales $j\ge 1$ is at most $3\sqrt{\mu\log(2R/\mu)}$, a bound depending only on the mass $\mu$ and not on the number of coordinates.
--
--   **Formalization Note** Here $\sqrt{\cdot}$ is `Real.sqrt` (which returns $0$ on negative arguments) and $\log$ is `Real.log`. At $s=0$ Lean evaluates $2R/0=0$ and $\log 0=0$, so the left-hand side is $0$. On the right-hand side $2R/\mu\ge 4$, so no convention is involved there.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L763-L808

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.dyadic_potential_bound {s μ R : ℝ} (hμ : 0 < μ) (hμR : 2 * μ ≤ R)
    (hs : 0 ≤ s) (j : ℕ) (hsmass : s ≤ 2 ^ j * μ) :
    Real.sqrt (s * Real.log (2 * R / s)) / 2 ^ j ≤
      (3 / 4) ^ j * Real.sqrt (μ * Real.log (2 * R / μ)) := by sorry
