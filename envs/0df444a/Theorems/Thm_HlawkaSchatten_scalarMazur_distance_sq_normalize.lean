-- Prove2me | Theorems.Thm_HlawkaSchatten_scalarMazur_distance_sq_normalize
-- name    : HlawkaSchatten.scalarMazur_distance_sq_normalize
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:18:52.88698+00:00
-- url     : https://prove2.me/theorems/ff45da22-b755-467f-8dbb-6c959c6467f8
-- title:
--   Homogeneity of the squared scalar Mazur distance under rescaling by the second argument
-- statement:
--   Let $p,a\in\mathbb R$ and $b\in\mathbb R$ with $b\neq0$. Write $\psi_p(x)=\operatorname{sgn}(x)|x|^{p/2}$ for the scalar Mazur map. Then
--
--   $$
--   \bigl(\psi_p(a)-\psi_p(b)\bigr)^{2}
--   = |b|^{p}\,\bigl(\psi_p(a/b)-1\bigr)^{2}.
--   $$
--
--   This is a homogeneity (rescaling) identity for the squared Mazur distance: dividing both arguments by $b$ and pulling out the resulting factor $|b|^p$ reduces any squared Mazur distance to one where the second argument is normalized to $1$. It lets later arguments about a scalar ratio at a general pair $(a,b)$ be reduced, after this normalization, to a function of the single real parameter $t=a/b$.
--
--   **Formalization Note.** No sign or size restriction is placed on $p$ or $a$; the identity holds for every real $p$ and $a$, using only $b\neq0$, because it follows purely from the positive homogeneity and oddness of $\psi_p$, both of which Lean's totalized real power and sign function satisfy unconditionally.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/ScalarRatio.lean#L457-L489

import Definitions.Def_HlawkaSchatten_ScalarBregman
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

theorem HlawkaSchatten.scalarMazur_distance_sq_normalize (p a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    (scalarMazur p a - scalarMazur p b) ^ 2 =
      |b| ^ p * (scalarMazur p (a / b) - 1) ^ 2 := by sorry
