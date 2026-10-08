-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_eq_9_8
-- name    : GoldieRenewal.Implicit.eq_9_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:27.506983+00:00
-- url     : https://prove2.me/theorems/825c993e-b4fb-4004-9461-e61d6d8feaf2
-- title:
--   (9.8), p. 145 — in Case 1, ř = ğ₁ ∗ ν with ν the renewal measure of η(du) = e^{κu}P(log|M| ∈ du)
-- statement:
--   Let $M$ satisfy the conditions of Lemma 2.2 with $M\ge0$ a.s., let $R$ be independent of $M$, and assume (2.8). Let
--   $$
--   r(t) = e^{\kappa t}P(R>e^t),\qquad g_1(t) = e^{\kappa t}\bigl(P(R>e^t)-P(MR>e^t)\bigr),
--   $$
--   let $\eta(du) = e^{\kappa u}P(\log|M|\in du)$ (no mass at $-\infty$) and let $\nu = \sum_{n\ge0}\eta^{(n)}$ be its renewal measure. Then for every $t\in\mathbb R$ the integral $\check g_1*\nu(t) = \int\check g_1(t-u)\,\nu(du)$ converges absolutely and
--   $$
--   \check r(t) = \check g_1*\nu(t).
--   $$
--
--   This is the renewal equation behind the implicit renewal theorem: the tail of $R$, in logarithmic scale and smoothed, is the renewal measure of the tilted walk $\log|M_1|+\dots+\log|M_k|$ applied to the smoothed tail difference.
--
--   **Formalization Note** $\eta$ and $\nu$ are built from the law of $M$ alone; $e^{\kappa t}P(V_k\in dt)$ of (9.7) equals $\eta^{(k)}(dt)$, so the i.i.d. copies $M_k$ of the proof do not appear.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, §9, proof of Theorem 2.3, Case 1, (9.7)–(9.8), p. 145

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_DRi
import Definitions.Def_GoldieRenewal_Implicit_TailConstants
import Definitions.Def_GoldieRenewal_Implicit_RenewalMeasures
open MeasureTheory ProbabilityTheory

namespace GoldieRenewal.Implicit

/-- **(9.8)** (Goldie 1991, Ann. Appl. Probab. 1(1), §9, proof of Theorem 2.3, Case 1, p. 145):
`ř = ğ₁ ∗ ν`, where `r(t) := e^{κt} P(R > e^t)` (9.3), `g₁(t) := e^{κt}(P(R > e^t) − P(MR > e^t))`
(3.5), `η(du) := e^{κu} P(log|M| ∈ du)` and `ν := Σ_{n≥0} η^{(n)}` is its renewal measure (9.7).

Setting: `M` satisfies the conditions of Lemma 2.2, `M ≥ 0` a.s. (Case 1), `R` is independent of
`M`, and (2.8) holds. Conclusion: for every `t ∈ ℝ` the integral `ğ₁ ∗ ν(t) = ∫ ğ₁(t − u) ν(du)`
converges absolutely and equals `ř(t)`.

**Formalization Note** `η` is `tiltedLaw κ (P.map M)` (the law of `log|M|` on `{M ≠ 0}`, tilted by
`e^{κu}`), defined from the law of `M` alone; the sequence `M₁, M₂, …` of the proof is not needed
in the statement, since `e^{κt} P(V_k ∈ dt) = η^{(k)}(dt)`. `ř` and `ğ₁` are `smooth` of `rFun` and
`gOne`. The absolute convergence (`Integrable … ν`) is part of the conclusion, as in the paper
("`|ğ₁| ∗ ν(t) < ∞` for all `t`"). -/
theorem eq_9_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (κ : ℝ)
    (hC : CramerConditions κ (P.map M)) (hind : IndepFun R M P)
    (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω) (h28 : TailCondPlus P M R κ) :
    ∀ t : ℝ,
      Integrable (fun u => smooth (gOne P M R κ) (t - u))
          (renewalMeasure (tiltedLaw κ (P.map M))) ∧
        smooth (rFun P R κ) t =
          convFun (smooth (gOne P M R κ)) (renewalMeasure (tiltedLaw κ (P.map M))) t := by sorry

end GoldieRenewal.Implicit
