-- Prove2me | Theorems.Thm_HlawkaSchatten_continuous_regularizedScalarRatio
-- name    : HlawkaSchatten.continuous_regularizedScalarRatio
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:18:08.819913+00:00
-- url     : https://prove2.me/theorems/c3a10f30-3c65-4b10-9be7-7f10914f55cb
-- title:
--   The regularized scalar Bregman-to-Mazur ratio is continuous on $\mathbb R$
-- statement:
--   Let $p\in\mathbb R$ with $p>1$. Write $\psi_p(x)=\operatorname{sgn}(x)|x|^{p/2}$ for the scalar Mazur map and
--
--   $$
--   \beta_p(a,b)=\frac{|a|^p}{p}-\frac{|b|^p}{p}-|b|^{p-2}b\,(a-b)
--   $$
--
--   for the Bregman divergence of the potential $|x|^p/p$. Define the raw ratio and its patched (regularized) version by
--
--   $$
--   \mathrm{ratio}_p(t)=\frac{\beta_p(t,1)}{(\psi_p(t)-1)^2},
--   \qquad
--   \mathrm{ratio}_p^{\mathrm{reg}}(t)=
--   \begin{cases}
--   \dfrac{2(p-1)}{p^{2}} & t=1,\\[4pt]
--   \mathrm{ratio}_p(t) & t\neq 1.
--   \end{cases}
--   $$
--
--   The raw ratio's denominator vanishes exactly at $t=1$, where its numerator also vanishes. We use Lean's convention that this $0/0$ has value $0$; the regularized ratio replaces that value with $2(p-1)/p^2$ and agrees with the raw ratio everywhere else. Then
--
--   $$
--   \mathrm{ratio}_p^{\mathrm{reg}} \text{ is continuous on } \mathbb R.
--   $$
--
--   This is the regularity fact that lets the argument extend the ratio continuously to the point at infinity of the one-point compactification of $\mathbb R$ and invoke compactness there to extract finite two-sided constants bounding $\beta_p$ by $(\psi_p(a)-\psi_p(b))^2$, uniformly over all real $a,b$.
--
--   **Formalization Note.** Both `scalarRatio` and `regularizedScalarRatio` are defined for every real input. The theorem establishes continuity of `regularizedScalarRatio`; its value at $1$ is the limit of the raw quotient through $t\neq1$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarRatio.lean#L397-L416

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

theorem HlawkaSchatten.continuous_regularizedScalarRatio {p : ℝ} (hp : 1 < p) :
    Continuous (regularizedScalarRatio p) := by sorry
