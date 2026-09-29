-- Prove2me | Theorems.Thm_HlawkaSchatten_finset_sum_scalarBregman_two_sided
-- name    : HlawkaSchatten.finset_sum_scalarBregman_two_sided
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:19:25.57708+00:00
-- url     : https://prove2.me/theorems/a298fe02-4fa8-4af1-a27a-5886a533d720
-- title:
--   Nonnegatively weighted finite-sum lift of the two-sided scalar Bregman-to-Mazur comparison
-- statement:
--   Let $\iota$ be a type, let $p,m,M\in\mathbb R$ with $p>1$, and write $\psi_p(x)=\operatorname{sgn}(x)|x|^{p/2}$ and
--
--   $$
--   \beta_p(a,b)=\frac{|a|^p}{p}-\frac{|b|^p}{p}-|b|^{p-2}b\,(a-b)
--   $$
--
--   for the scalar Mazur map and the Bregman divergence of the potential $|x|^p/p$. Let $\mathbb R\cup\{\infty\}$ be the one-point compactification of $\mathbb R$, extend the scalar ratio there by $\mathrm{ratio}_p^{\mathrm c}(x)=\beta_p(x,1)/(\psi_p(x)-1)^2$ for finite $x\neq1$, by $2(p-1)/p^2$ at $x=1$, and by $1/p$ at $x=\infty$, and suppose
--
--   $$
--   m\le \mathrm{ratio}_p^{\mathrm c}(x)\le M \qquad\text{for every } x\in\mathbb R\cup\{\infty\}.
--   $$
--
--   Let $s$ be a finite subset of $\iota$, let $w,a,b:\iota\to\mathbb R$, and suppose $w_i\ge0$ for every $i\in s$. Then
--
--   $$
--   m\sum_{i\in s} w_i\bigl(\psi_p(a_i)-\psi_p(b_i)\bigr)^{2}
--   \;\le\; \sum_{i\in s} w_i\,\beta_p(a_i,b_i)
--   \;\le\; M\sum_{i\in s} w_i\bigl(\psi_p(a_i)-\psi_p(b_i)\bigr)^{2}.
--   $$
--
--   This lifts the pointwise scalar two-sided comparison to a nonnegatively-weighted finite sum, term by term, without changing the constants $m,M$. It is exactly the ordered-algebraic step needed once Bregman and squared-Mazur quantities attached to a pair of Hermitian operators have each been decomposed as a sum over pairs of eigenbasis vectors, weighted by nonnegative basis-overlap coefficients.
--
--   **Formalization Note.** $\iota$ need not be finite or carry any structure; only the subset $s$ is required to be finite, and the weights $w$, arguments $a,b$ are arbitrary functions out of $\iota$, unconstrained outside $s$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/SpectralLift.lean#L21-L48

import Definitions.Def_HlawkaSchatten_ScalarBregman
import Definitions.Def_HlawkaSchatten_ScalarRatio
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Nonnegative weighted lift of the scalar comparison

The Hermitian spectral argument writes both divergences as finite sums with
weights `Tr(Pᵢ Qⱼ) ≥ 0`.  This file isolates the ordered-algebraic step which
lifts the pointwise scalar bounds through those sums.
-/


open scoped InnerProductSpace

open HlawkaSchatten

theorem HlawkaSchatten.finset_sum_scalarBregman_two_sided {ι : Type*} {p m M : ℝ}
    (hp : 1 < p)
    (hbound : ∀ x : OnePoint ℝ, m ≤ compactifiedScalarRatio p x ∧
      compactifiedScalarRatio p x ≤ M) (s : Finset ι) (w a b : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    m * ∑ i ∈ s, w i * (scalarMazur p (a i) - scalarMazur p (b i)) ^ 2 ≤
        ∑ i ∈ s, w i * scalarBregman p (a i) (b i) ∧
      ∑ i ∈ s, w i * scalarBregman p (a i) (b i) ≤
        M * ∑ i ∈ s, w i * (scalarMazur p (a i) - scalarMazur p (b i)) ^ 2 := by sorry
