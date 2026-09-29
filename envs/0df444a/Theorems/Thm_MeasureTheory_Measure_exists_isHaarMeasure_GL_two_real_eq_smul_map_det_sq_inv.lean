-- Prove2me | Theorems.Thm_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv
-- name    : MeasureTheory.Measure.exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/3f519591-c157-536b-ba86-421b109a2f0c
-- title:
--   Haar measure on GL₂(ℝ) is (det)⁻² dA up to scalar
-- statement:
--   Let $\mathrm{GL}(\mathrm{Fin}\,2,\mathbb{R})$, the group of units of the ring of $2\times 2$ real matrices, carry a measurable space structure which is the Borel $\sigma$-algebra of its topology, and let $\mu$ be a Haar measure on it in the sense of Mathlib's `MeasureTheory.Measure.IsHaarMeasure` (left invariant, regular, positive on nonempty open sets and finite on compact sets). The assertion is that there exists a constant $c$ in $\mathbb{R}_{\ge 0}$ with $0 < c$ such that $\mu$ equals $c$ times the following measure: take Lebesgue measure `volume` on the space $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{R}$ of real $2\times 2$ arrays (the fourfold product of Lebesgue measure on the entries), restrict it to the set of arrays $A$ with $\det A \neq 0$, weight it by the density $A \mapsto \mathrm{ofReal}\big(((\det A)^2)^{-1}\big)$ with values in $[0,\infty]$, and push the resulting measure forward along the map sending an array $A$ with $\det A \neq 0$ to the corresponding element `Matrix.GeneralLinearGroup.mkOfDetNeZero` of $\mathrm{GL}_2(\mathbb{R})$ and sending every array of determinant $0$ to the identity element. Thus $d\mu(g) = c\,(\det g)^{-2}\prod_{i,j} dg_{ij}$; the weight is $(\det)^{-2}$, not $|\det|^{-2}$, these agreeing in dimension $2$.
--
--   This is the explicit description of Haar measure on $\mathrm{GL}_2(\mathbb{R})$ in matrix-entry coordinates, obtained from uniqueness of Haar measure up to a positive scalar. It is used in the computation of orbital integrals on $\mathrm{GL}_2(\mathbb{R})$, where the split and elliptic transforms are evaluated against this coordinate form of the measure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_Measure_exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv.lean

import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Constructions
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory

theorem MeasureTheory.Measure.exists_isHaarMeasure_GL_two_real_eq_smul_map_det_sq_inv
    [MeasurableSpace (GL (Fin 2) ℝ)] [BorelSpace (GL (Fin 2) ℝ)]
    (μ : Measure (GL (Fin 2) ℝ)) [μ.IsHaarMeasure] :
    ∃ c : NNReal, 0 < c ∧
      μ = c • Measure.map
        (fun A : Fin 2 → Fin 2 → ℝ =>
          if h : (Matrix.of A).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of A) h
          else 1)
        ((volume.restrict {A : Fin 2 → Fin 2 → ℝ | (Matrix.of A).det ≠ 0}).withDensity
          fun A => ENNReal.ofReal (((Matrix.of A).det ^ 2)⁻¹)) := by sorry
