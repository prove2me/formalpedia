-- Prove2me | Theorems.Thm_HryniewiczCriterion_exists_periodic_time_change
-- name    : HryniewiczCriterion.exists_periodic_time_change
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-06T19:53:36.143056+00:00
-- url     : https://prove2.me/theorems/a78c7bc3-2afb-4ed1-9106-03a0793051cf
-- title:
--   Time change with a positive periodic rate
-- statement:
--   Let $m:\mathbb{R}\to\mathbb{R}$ be continuous, positive and $T$-periodic with $T>0$. Then $\tau(s)=\int_0^s m$ is a strictly increasing homeomorphism of $\mathbb{R}$. Its inverse $\sigma$ is continuous and strictly increasing, with $\sigma(0)=0$ and $\sigma'(t)=1/m(\sigma(t))$. Moreover, with $Q_T=\tau(T)>0$, we have $\sigma(t+Q_T)=\sigma(t)+T$.
--
--   This is the time change that turns a $T$-periodic orbit $x$ of $X_H$ into the $Q_T$-periodic orbit $x\circ\sigma$ of $X_K=c\,X_H$ when $c>0$ (take $m=1/c\circ x$).
-- source:
--   Standard time change of a periodic orbit under a positive rescaling of the vector field, as in Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, Section 3, (3.31)–(3.32), p. 219 (passing from H to the homogeneous K with the same level set); scalar companion of the platform theorems TimeChange.positive_time_change_flow / compact_positive_time_change_flow.

import Definitions.Def_HryniewiczCriterion_GraphAngle

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.exists_periodic_time_change (m : ℝ → ℝ) (hm : Continuous m) (hpos : ∀ s, 0 < m s) (T : ℝ)
    (hT : 0 < T) (hper : ∀ s, m (s + T) = m s) :
    ∃ (τf σ : ℝ → ℝ) (QT : ℝ), 0 < QT ∧ Continuous τf ∧ Continuous σ ∧ StrictMono τf ∧
      StrictMono σ ∧ (∀ t, τf (σ t) = t) ∧ (∀ s, σ (τf s) = s) ∧ τf 0 = 0 ∧ σ 0 = 0 ∧
      τf T = QT ∧ (∀ t, σ (t + QT) = σ t + T) ∧ ∀ t, HasDerivAt σ (m (σ t))⁻¹ t := by sorry
