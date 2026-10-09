-- Prove2me | Theorems.Thm_HairerLiFBM_SemiDet_lemma_2_1
-- name    : HairerLiFBM.SemiDet.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:00.578524+00:00
-- url     : https://prove2.me/theorems/f0c1e4ec-da4c-4110-85a7-a22697629a33
-- title:
--   Lemma 2.1 — composition estimate in Hölder seminorm
-- statement:
--   Let $F:\mathbb R^d\to\mathbb R$ have two bounded derivatives and let $0<\alpha<1$. On any time interval, the Hölder seminorm of the difference of compositions obeys
--
--   $$|F(x)-F(y)|_\alpha \le C\left(|F'|_\infty |x-y|_\alpha + |F''|_\infty |x-y|_\infty (|x|_\alpha+|y|_\alpha)\right).$$
--
--   Here $C$ is a universal constant, independent of $d$, the interval, $F$, and the paths. This is the composition estimate used for the deterministic Young-equation argument.
--
--   **Formalization Note** The derivative bounds are explicit constants $K_1,K_2$. Seminorms and sup norms take values in $[0,\infty]$, so the assertion also has a defined meaning when a path has infinite seminorm.
-- source:
--   Hairer and Li, Averaging dynamics driven by fractional Brownian motion, Ann. Probab. 48(4) (2020), https://doi.org/10.1214/19-AOP1408, p. 1829, Lemma 2.1

import Mathlib
import Definitions.Def_HairerLiFBM_SemiDet_Model

namespace HairerLiFBM.SemiDet

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Lemma 2.1, p. 1829: the Hölder composition estimate. -/
theorem lemma_2_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (α : ℝ), 0 < d → 0 < α → α < 1 →
      ∀ (F : E d → ℝ) (K1 K2 : ℝ), ContDiff ℝ 2 F →
        (∀ z, ‖fderiv ℝ F z‖ ≤ K1) →
        (∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ K2) →
        ∀ (a b : ℝ) (x y : ℝ → E d),
          holderSemi α (Set.Icc a b) x < ⊤ →
          holderSemi α (Set.Icc a b) y < ⊤ →
          holderSemi α (Set.Icc a b) (fun t => F (x t) - F (y t)) ≤
            ENNReal.ofReal C *
              (ENNReal.ofReal K1 * holderSemi α (Set.Icc a b) (fun t => x t - y t) +
                ENNReal.ofReal K2 * supNorm (Set.Icc a b) (fun t => x t - y t) *
                  (holderSemi α (Set.Icc a b) x + holderSemi α (Set.Icc a b) y)) := by sorry

end HairerLiFBM.SemiDet
