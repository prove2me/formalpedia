-- Prove2me | Theorems.Thm_MultivarScores_LevelSet_strictly_consistent
-- name    : MultivarScores.LevelSet.strictly_consistent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:35:02.383527+00:00
-- url     : https://prove2.me/theorems/6f029daa-6033-478b-85fd-c1e5a1a4d512
-- title:
--   Theorem 2 (p. 13), (20) (p. 34) — (S′)^Γ is strictly consistent when 𝓛^d{f_Y ∗ w = α} = 0 and h ≠ 0 a.e.
-- statement:
--   Let $P_Y$, $w$, $h$, $\alpha>0$ and the Borel set $A$ be as in Theorem 2: $w,h$ measurable and nonnegative, $h$ integrable, and $(s,z)\mapsto w(z-s)h(z)$ integrable for $P_Y\otimes\mathcal L^d$. Write $L=L(f_Y*w;\alpha)$. Assume moreover
--
--   1. $h(z)\neq0$ for $\mathcal L^d$-almost every $z$;
--   2. the set $\{z : (f_Y*w)(z)=\alpha\}$ is $\mathcal L^d$-null;
--   3. $A$ and $L$ differ by a set that is not $\mathcal L^d$-null, i.e. $\mathcal L^d(A\,\triangle\,L)\neq0$.
--
--   Then
--
--   $$\mathbb E_{P_Y}\bigl[(S')^\Gamma(L,\bullet;w,h,\alpha)\bigr]<\mathbb E_{P_Y}\bigl[(S')^\Gamma(A,\bullet;w,h,\alpha)\bigr].$$
--
--   So $L(f_Y*w;\alpha)$ is the unique minimizer of the expected level set score, up to $\mathcal L^d$-null sets: the strict consistency clause of Theorem 2.
--
--   **Formalization Note** The paper states strict consistency under the hypothesis "$L(f_Y*w;\alpha)$ equals the closure of $\{f_Y*w>\alpha\}$", and its proof (p. 34) uses only the consequence that $\{f_Y*w=\alpha\}$ is $\mathcal L^d$-null; that implication is false (for $d=1$, $P_Y=\delta_0$, $w=\alpha+\mathrm{dist}(\cdot,C)$ with $C\subset[0,1]$ a fat Cantor set and $h$ a Gaussian density, $L=\mathbb R$ is the closure of $\{w>\alpha\}$ but $\{w=\alpha\}=C$ has positive measure and $A=\mathbb R\setminus C$ scores the same as $L$), so the hypothesis the proof actually uses, item 2, replaces the printed closure condition. The proof's "$h>0$ by Assumption 1(c)" is Theorem 2's own hypothesis "$h$ is nonzero $\mathcal L^d$-a.e." (item 1). "Only minimizer" is read modulo null sets, as in the proof. The paper allows $w$ to be a local Borel measure (Assumption 1(a)); here $w$ is a measurable function, a disclosed specialization that excludes only the Dirac kernel $w=\delta_0$ (the density level set score (12)).
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 13, Theorem 2 (strict consistency sentence); p. 34, display (20) and the paragraph after it

import Mathlib
import Definitions.Def_MultivarScores_LevelSet_Setting

namespace MultivarScores.LevelSet

open MeasureTheory

theorem strictly_consistent {d : ℕ} (w h : MultivarScores.L2Rule.E d → ℝ) (PY : Measure (MultivarScores.L2Rule.E d))
    [IsProbabilityMeasure PY]
    (hw_meas : Measurable w) (hw_nonneg : ∀ z, 0 ≤ w z)
    (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z) (hh_int : Integrable h)
    (hwh_int : Integrable (fun p : MultivarScores.L2Rule.E d × MultivarScores.L2Rule.E d => w (p.2 - p.1) * h p.2) (PY.prod volume))
    (α : ℝ) (hα : 0 < α) (A : Set (MultivarScores.L2Rule.E d)) (hA : MeasurableSet A)
    (hh_ne : ∀ᵐ z, h z ≠ 0)
    (hnull : volume {z | MultivarScores.L2Rule.smooth PY w z = α} = 0)
    (hdiff : volume (symmDiff A (levelSet (MultivarScores.L2Rule.smooth PY w) α)) ≠ 0) :
    ∫ y, scoreΓ w h α (levelSet (MultivarScores.L2Rule.smooth PY w) α) y ∂PY < ∫ y, scoreΓ w h α A y ∂PY := by sorry

end MultivarScores.LevelSet
