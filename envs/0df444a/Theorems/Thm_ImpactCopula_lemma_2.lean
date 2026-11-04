-- Prove2me | Theorems.Thm_ImpactCopula_lemma_2
-- name    : ImpactCopula.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:38.521845+00:00
-- url     : https://prove2.me/theorems/c0a3d253-cdfc-4fcb-ab9e-0cf025681dd4
-- title:
--   Lemma 2 — restricting the inverse to $\overline{\mathcal R}_\theta$ does not change $F_\theta^{-1}$
-- statement:
--   Let $(X_i,\theta_i)$ have joint law $\mu$ on $\mathbb R^2$, with $F_\theta$ the distribution function of $\theta_i$ and $\overline{\mathcal R}_\theta$ the closure of its range. Let $f : \mathbb R \to [0,1]$ be a distribution function and, for $w \in [0,1]$,
--
--   $$
--   \underline f^{-1}(w) = \inf\{v : f(v) \ge w,\ v \in \overline{\mathcal R}_\theta\}, \qquad f^{-1}(w) = \inf\{v : f(v) \ge w\}.
--   $$
--
--   Then:
--
--   1. for every $w \in [0,1]$, $\;F_\theta^{-1}\big(\underline f^{-1}(w)\big) = F_\theta^{-1}\big(f^{-1}(w)\big)$;
--   2. for every $v \in \overline{\mathcal R}_\theta$, $\;\{w \in [0,1] : \underline f^{-1}(w) \le v\} = \{w \in [0,1] : w \le f(v)\}$.
--
--   Here $F_\theta^{-1}(p) = \inf\{x : F_\theta(x) \ge p\}$, and all infima take values in $[-\infty, +\infty]$ with $\inf\emptyset = +\infty$.
--
--   Part (i) lets the proof of Theorem 2 replace $g_u$ by its restriction to $\overline{\mathcal R}_\theta$ without changing $g$; part (ii) converts events $\{\tilde g_u(V) \le F_\theta(y)\}$ into $\{V \le \tilde D_1 C(u, F_\theta(y))\}$.
--
--   Differences from the source:
--   - encoding: inverses taking the values $\pm\infty$ → `EReal`-valued `genInvE`, `restrInvE`, with $F_\theta^{-1}$ applied to an extended-real argument; reason: the paper's convention, written in Lean; with real `sInf ∅ = 0` part (ii) would be false.
--   - encoding: $\{w : \dots\}$ in (ii) → $\{w \in [0,1] : \dots\}$; reason: $\underline f^{-1}$ is defined for $w \in [0,1]$ only.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Lemma 2, p.75 (PDF p.78)

import Mathlib
import Definitions.Def_ImpactCopula_cdfTheta
import Definitions.Def_ImpactCopula_rbarTheta
import Definitions.Def_ImpactCopula_IsDistributionFunction
import Definitions.Def_ImpactCopula_genInvE
import Definitions.Def_ImpactCopula_restrInvE

open MeasureTheory

namespace ImpactCopula

/-- **Lemma 2**, Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.75 (PDF p.78): "Given a distribution function f : ℝ → [0, 1], define
f̲⁻¹(w) = inf{v : f(v) ≥ w, v ∈ R̄_θ} for w ∈ [0, 1]. Then, we have: (i) For any w ∈ [0, 1],
F_θ⁻¹ ∘ f̲⁻¹(w) = F_θ⁻¹ ∘ f⁻¹(w); (ii) For any v ∈ R̄_θ, {w : f̲⁻¹(w) ≤ v} = {w : w ≤ f(v)}."

**Formalization Note.** All three inverses are taken in `EReal` (`genInvE`, `restrInvE`), the
paper's convention, in which an empty set has infimum `+∞` and a set unbounded below `−∞`; with
Lean's real `sInf ∅ = 0`, part (ii) would be false. `f⁻¹` and `F_θ⁻¹` are the inverse function
of Definition A.1 (p.42). `R̄_θ` and `F_θ` are those of the second marginal of the law `μ`. In
(ii) both sets are subsets of `[0, 1]`, the domain of `f̲⁻¹`. -/
theorem lemma_2 (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hf : IsDistributionFunction f) :
    (∀ w ∈ Set.Icc (0 : ℝ) 1,
        genInvE (cdfTheta μ) (restrInvE (rbarTheta μ) f w) =
          genInvE (cdfTheta μ) (genInvE f (w : EReal))) ∧
      ∀ v ∈ rbarTheta μ,
        {w : ℝ | w ∈ Set.Icc (0 : ℝ) 1 ∧ restrInvE (rbarTheta μ) f w ≤ (v : EReal)} =
          {w : ℝ | w ∈ Set.Icc (0 : ℝ) 1 ∧ w ≤ f v} := by sorry

end ImpactCopula
