-- Prove2me | Theorems.Thm_LeJEPA_hyperspherical_cramer_wold
-- name    : LeJEPA.hyperspherical_cramer_wold
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:01:44.700367+00:00
-- url     : https://prove2.me/theorems/7462e19a-dd42-42d5-a287-4dc881ef517c
-- title:
--   Lemma 3: hyperspherical Cramér–Wold
-- statement:
--   Let $d\in\mathbb{N}$.
--
--   1. Two probability measures $\mu,\nu$ on $\mathbb{R}^d$ are equal if and only if, for every unit vector $u\in\mathbb{S}^{d-1}$, the laws of $x\mapsto\langle u,x\rangle$ under $\mu$ and under $\nu$ coincide.
--   2. A sequence of probability measures $\mu_n$ on $\mathbb{R}^d$ converges weakly to $\mu$ if and only if, for every unit vector $u$, the one-dimensional projections $\langle u,\cdot\rangle_\#\mu_n$ converge weakly to $\langle u,\cdot\rangle_\#\mu$.
--
--   This is what lets a test along one-dimensional directions identify a high-dimensional distribution.
-- source:
--   Balestriero and LeCun, LeJEPA: Provable and Scalable Self-Supervised Learning Without the Heuristics, arXiv:2511.08544v3 (2025), Section 4.1, Lemma 3, proof in Appendix B.8

import Mathlib
import Definitions.Def_LeJEPA_Basic

open MeasureTheory Matrix Filter Topology
open scoped ENNReal InnerProductSpace

namespace LeJEPA

theorem hyperspherical_cramer_wold {d : ℕ} :
    (∀ μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)),
      ((∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
          (μ : Measure _).map (fun x => ⟪u, x⟫_ℝ) = (ν : Measure _).map (fun x => ⟪u, x⟫_ℝ)) ↔ μ = ν)) ∧
    (∀ (μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))),
      Tendsto μs atTop (𝓝 μ) ↔
      ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 →
        Tendsto (fun n => (μs n).map (f := fun x => ⟪u, x⟫_ℝ) (by fun_prop)) atTop
          (𝓝 (μ.map (f := fun x => ⟪u, x⟫_ℝ) (by fun_prop)))) := by sorry

end LeJEPA
