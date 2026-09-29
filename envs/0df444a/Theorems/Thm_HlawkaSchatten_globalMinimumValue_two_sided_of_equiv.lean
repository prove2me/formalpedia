-- Prove2me | Theorems.Thm_HlawkaSchatten_globalMinimumValue_two_sided_of_equiv
-- name    : HlawkaSchatten.globalMinimumValue_two_sided_of_equiv
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:20:26.731427+00:00
-- url     : https://prove2.me/theorems/79005d54-2ecf-45e9-86d7-79d2f0fe6e2d
-- title:
--   Transporting a two-sided comparison between global minima across an equivalence
-- statement:
--   Let $A$ and $B$ be two types related by a bijection $e:A\to B$ (an equivalence, `Equiv`), and let $f:A\to\mathbb R$ and $g:B\to\mathbb R$ be any two real-valued functions. Say a real number $v$ is the *global minimum value* of a function $h$ when $v\le h(x)$ for every $x$ in the domain and $h(x)=v$ for at least one $x$ (`IsGlobalMinimumValue`).
--
--   Let $\mathrm{fmin}$ be the global minimum value of $f$ and $\mathrm{gmin}$ the global minimum value of $g$, and let $m,M\in\mathbb R$ with $m\ge0$. Suppose that, for every $x\in A$,
--
--   $$
--   m\cdot g(e(x)) \;\le\; f(x) \;\le\; M\cdot g(e(x)).
--   $$
--
--   Then the same two-sided comparison holds between the two minimum values themselves:
--
--   $$
--   m\cdot\mathrm{gmin} \;\le\; \mathrm{fmin} \;\le\; M\cdot\mathrm{gmin}.
--   $$
--
--   This is a general transport principle: whenever two real-valued objectives on domains matched up by a bijection satisfy a pointwise two-sided linear comparison at every point, and each objective attains its own global minimum, the same two-sided comparison automatically passes to the two attained minimum values, with no further argument about where either minimum is attained. It is the kind of step needed whenever a pair of variational objectives in this construction turn out to be indexed by two different but equivalent index sets or spheres, so that a pointwise bound between the objectives can be promoted directly to a bound between the deficits their minima compute.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/Variational.lean#L40-L60

import Definitions.Def_HlawkaSchatten_Variational
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Variational minima for the Bregman--Mazur argument

This file proves two reusable parts of the variational layer.  First, a
pointwise two-sided comparison transports to attained global minima, even
when the two objectives are indexed by different but equivalent spheres.
Second, the weighted squared-distance objective on a Hilbert unit sphere has
the exact minimum used in the Schatten argument.
-/


open scoped InnerProductSpace ComplexConjugate

open HlawkaSchatten

theorem HlawkaSchatten.globalMinimumValue_two_sided_of_equiv
    {A B : Type*} (e : A ≃ B) (f : A → ℝ) (g : B → ℝ)
    (fmin gmin m M : ℝ) (hm : 0 ≤ m)
    (hf : IsGlobalMinimumValue f fmin)
    (hg : IsGlobalMinimumValue g gmin)
    (hcompare : ∀ x, m * g (e x) ≤ f x ∧ f x ≤ M * g (e x)) :
    m * gmin ≤ fmin ∧ fmin ≤ M * gmin := by sorry
