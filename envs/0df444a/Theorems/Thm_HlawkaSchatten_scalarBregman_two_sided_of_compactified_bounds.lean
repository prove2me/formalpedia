-- Prove2me | Theorems.Thm_HlawkaSchatten_scalarBregman_two_sided_of_compactified_bounds
-- name    : HlawkaSchatten.scalarBregman_two_sided_of_compactified_bounds
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:19:05.724401+00:00
-- url     : https://prove2.me/theorems/3f1a3e39-7822-4d71-98f6-d67e35583f03
-- title:
--   A global bound on the compactified scalar ratio gives a two-sided Bregman-to-Mazur comparison
-- statement:
--   Let $p,m,M\in\mathbb R$ with $p>1$. Write $\psi_p(x)=\operatorname{sgn}(x)|x|^{p/2}$ for the scalar Mazur map and
--
--   $$
--   \beta_p(a,b)=\frac{|a|^p}{p}-\frac{|b|^p}{p}-|b|^{p-2}b\,(a-b)
--   $$
--
--   for the Bregman divergence of the potential $|x|^p/p$. Let $\mathbb R\cup\{\infty\}$ denote the one-point (Alexandroff) compactification of $\mathbb R$, and define the compactified ratio there by
--
--   $$
--   \mathrm{ratio}_p^{\mathrm c}(x)=
--   \begin{cases}
--   \dfrac{2(p-1)}{p^{2}} & x=1,\\[4pt]
--   \dfrac{\beta_p(x,1)}{(\psi_p(x)-1)^2} & x\in\mathbb R,\ x\neq 1,\\[4pt]
--   \dfrac1p & x=\infty.
--   \end{cases}
--   $$
--
--   Suppose $m\le \mathrm{ratio}_p^{\mathrm c}(x)\le M$ for every $x\in\mathbb R\cup\{\infty\}$. Then, for every $a,b\in\mathbb R$,
--
--   $$
--   m\,\bigl(\psi_p(a)-\psi_p(b)\bigr)^{2} \;\le\; \beta_p(a,b)
--   \;\le\; M\,\bigl(\psi_p(a)-\psi_p(b)\bigr)^{2}.
--   $$
--
--   This is the scalar comparison that later gets lifted, term by term through a spectral decomposition, to bound the trace-level Bregman divergence between two Hermitian operators by their squared Hilbert–Schmidt Mazur distance, uniformly in the dimension: the constants $m,M$ pass through that lift unchanged.
--
--   **Formalization Note.** The hypothesis quantifies over the whole compactified line, including the point at infinity; no compactness or continuity argument is repeated inside this theorem.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarRatio.lean#L565-L598

import Definitions.Def_HlawkaSchatten_ScalarBregman
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

theorem HlawkaSchatten.scalarBregman_two_sided_of_compactified_bounds {p m M : ℝ} (hp : 1 < p)
    (hbound : ∀ x : OnePoint ℝ, m ≤ compactifiedScalarRatio p x ∧
      compactifiedScalarRatio p x ≤ M) (a b : ℝ) :
    m * (scalarMazur p a - scalarMazur p b) ^ 2 ≤ scalarBregman p a b ∧
      scalarBregman p a b ≤ M * (scalarMazur p a - scalarMazur p b) ^ 2 := by sorry
