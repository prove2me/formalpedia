-- Prove2me | Theorems.Thm_HlawkaSchatten_tendsto_scalarRatio_one
-- name    : HlawkaSchatten.tendsto_scalarRatio_one
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:17:56.767585+00:00
-- url     : https://prove2.me/theorems/92f74e1e-38b2-4232-a2e0-cdd9b8057153
-- title:
--   The scalar Bregman-to-Mazur ratio has removable-singularity limit $2(p-1)/p^2$ at $t=1$
-- statement:
--   Let $p\in\mathbb R$ with $p>1$. Write $\psi_p(x)=\operatorname{sgn}(x)|x|^{p/2}$ for the scalar Mazur map,
--
--   $$
--   \beta_p(a,b)=\frac{|a|^p}{p}-\frac{|b|^p}{p}-|b|^{p-2}b\,(a-b)
--   $$
--
--   for the Bregman divergence of the potential $|x|^p/p$, and
--
--   $$
--   \mathrm{ratio}_p(t)=\frac{\beta_p(t,1)}{(\psi_p(t)-1)^2}
--   $$
--
--   for their quotient. At $t=1$, both the numerator and denominator vanish; we use Lean's convention that the resulting $0/0$ has value $0$. The theorem concerns the limit as $t$ approaches $1$ through values different from $1$:
--
--   $$
--   \mathrm{ratio}_p(t) \;\longrightarrow\; \frac{2(p-1)}{p^{2}}.
--   $$
--
--   This is exactly the value installed at $t=1$ to produce a continuous regularized ratio on all of $\mathbb R$, which is in turn the fact used to extend the ratio to the one-point compactification of $\mathbb R$ and extract finite two-sided bounds by compactness.
--
--   **Formalization Note.** The raw function `scalarRatio` has value $0$ at $t=1$. The limit along $t\neq1$ is independent of this assigned value; `regularizedScalarRatio` replaces it with $2(p-1)/p^2$. The explanation gives the double L'Hopital argument for this limit.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarRatio.lean#L260-L341

import Definitions.Def_HlawkaSchatten_ScalarRatio
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The scalar Bregman--Mazur ratio

This file starts the compact scalar-reduction layer of the Schatten Hlawka
argument.  The raw quotient has a removable singularity at `t = 1`; the
regularized version installs its second-order limiting value.
-/


open Filter Set
open scoped OnePoint Topology

open HlawkaSchatten

theorem HlawkaSchatten.tendsto_scalarRatio_one {p : ℝ} (hp : 1 < p) :
    Tendsto (scalarRatio p) (𝓝[≠] 1) (𝓝 (2 * (p - 1) / p ^ 2)) := by sorry
