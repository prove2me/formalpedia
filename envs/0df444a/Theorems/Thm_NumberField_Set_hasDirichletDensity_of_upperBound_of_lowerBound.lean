-- Prove2me | Theorems.Thm_NumberField_Set_hasDirichletDensity_of_upperBound_of_lowerBound
-- name    : NumberField.Set.hasDirichletDensity_of_upperBound_of_lowerBound
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:39:45.847405+00:00
-- url     : https://prove2.me/theorems/950f7e61-c963-4274-8832-e01b7b9b70e7
-- title:
--   Matching upper and lower bounds determine Dirichlet density
-- statement:
--   Let $K$ be a number field, let $S$ be a set of its nonzero prime ideals, and let $\delta\in\mathbb R$. For $s>1$ put
--
--   $$
--   R_S(s)=\frac{\sum_{\mathfrak p\in S}(N\mathfrak p)^{-s}}{\sum_{\mathfrak p}(N\mathfrak p)^{-s}}.
--   $$
--
--   Suppose that for every $\varepsilon>0$, both $R_S(s)<\delta+\varepsilon$ and $\delta-\varepsilon<R_S(s)$ hold for all $s>1$ sufficiently close to one. Then
--
--   $$
--   \lim_{s\to1^+}R_S(s)=\delta.
--   $$
--
--   Thus $S$ has Dirichlet density $\delta$.
--
--   This combines matching one-sided estimates into the existence of a Dirichlet density.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/DirichletDensityBounds.lean#L229-L252) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/DirichletDensityBounds.lean#L229-L252

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_DirichletDensityBounds
import Mathlib.NumberTheory.NumberField.DirichletDensity

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# One-sided bounds for Dirichlet density

For a set `S` of nonzero prime ideals of a number field, Mathlib's
`NumberField.Set.HasDirichletDensity S δ` says that the ratio

`S.primeIdealZetaSum s / Set.univ.primeIdealZetaSum s`

tends to `δ` as `s` approaches `1` from the right.  Squeeze arguments often produce the two
sides of this limit separately.  This file records those one-sided conclusions as
`NumberField.Set.IsLowerDirichletDensityBound S δ` and
`NumberField.Set.IsUpperDirichletDensityBound S δ`.

The predicates use eventual epsilon inequalities, rather than assigning junk-valued lower and
upper densities.  They are monotone in the proposed bound, and a common lower and upper bound
forces a Dirichlet density.  A lower bound is always at most an upper bound; this
comparison also gives the natural interval restrictions on one-sided bounds.

## Main results

* `NumberField.Set.hasDirichletDensity_iff`: Mathlib's `HasDirichletDensity`, unfolded to the
  convergence of the defining ratio.
* `NumberField.Set.HasDirichletDensity.isLowerDirichletDensityBound` and
  `NumberField.Set.HasDirichletDensity.isUpperDirichletDensityBound`: a Dirichlet density is
  both a lower and an upper bound.
* `NumberField.Set.isLowerDirichletDensityBound_of_forall_lt` and
  `NumberField.Set.isUpperDirichletDensityBound_of_forall_gt`: a value is a lower (upper) bound as
  soon as every smaller (larger) value is.
* `NumberField.Set.IsLowerDirichletDensityBound.le_of_isUpperDirichletDensityBound`:
  every lower bound is at most every upper bound.
* `NumberField.Set.hasDirichletDensity_of_upperBound_of_lowerBound`: matching one-sided bounds
  force a Dirichlet density.
* `NumberField.Set.hasDirichletDensity_iff_bounds`: the resulting characterization of
  Dirichlet density.

## References

* J.-P. Serre, *Corps locaux*, Chapter VI.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

 section

open _root_.Filter _root_.IsDedekindDomain _root_.NumberField
open scoped _root_.Topology

namespace NumberField.Set
end NumberField.Set
section NumberField.Set
open NumberField NumberField.Set

variable {K : Type*} [Field K] [NumberField K]













-- The proof below follows `NumberField.Set.HasDirichletDensity.le_one` from
-- `Mathlib.NumberTheory.NumberField.DirichletDensity`.

theorem NumberField.Set.hasDirichletDensity_of_upperBound_of_lowerBound
    {S : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (hupper : _root_.NumberField.Set.IsUpperDirichletDensityBound S δ)
    (hlower : _root_.NumberField.Set.IsLowerDirichletDensityBound S δ) :
    S.HasDirichletDensity δ := by sorry
