-- Prove2me | Theorems.Thm_MultivarScores_L2Rule_mcrps_strictly_proper
-- name    : MultivarScores.L2Rule.mcrps_strictly_proper
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:30:40.897219+00:00
-- url     : https://prove2.me/theorems/17d63217-cb0b-4cbf-afdb-337dae17843a
-- title:
--   §3.2.2, p. 11 — MCRPS (5) and MCRPS′ (6) are strictly proper if h is nonzero 𝓛^d-a.e.
-- statement:
--   Let $h:\mathbb R^d\to\mathbb R$ be measurable, nonnegative, integrable, and nonzero $\mathcal L^d$-almost everywhere. Let $P_X\ne P_Y$ be any two probability distributions on $\mathbb R^d$, with CDFs $F_X,F_Y$. Then the multivariate CRPS (5) and its equivalent form (6) are strictly proper:
--
--   $$\mathbb E_{P_Y}\big[\mathrm{MCRPS}(P_Y,\bullet;h)\big]<\mathbb E_{P_Y}\big[\mathrm{MCRPS}(P_X,\bullet;h)\big],\qquad \mathbb E_{P_Y}\big[\mathrm{MCRPS}'(P_Y,\bullet;h)\big]<\mathbb E_{P_Y}\big[\mathrm{MCRPS}'(P_X,\bullet;h)\big].$$
--
--   MCRPS is the L² score (2) with the Heaviside kernel $w=u$, for which $f_X*u=F_X$; the paper's reason for strictness is that the CDF uniquely characterizes a distribution. No integrability condition on $P_X,P_Y$ is needed: since $0\le F\le1$ and $h$ is integrable, both scores "can be used with all distributions".
--
--   **Formalization Note** The statement is for every dimension $d$, not only $d=1$. $h$ is only assumed nonnegative and integrable (the paper's sentence takes $h$ to be a PDF for the second claim; a PDF is a special case).
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 10, (5), (6); p. 11, first paragraph

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting

namespace MultivarScores.L2Rule

open MeasureTheory

/-- §3.2.2, p. 11: if `h` is nonnegative, integrable and nonzero `𝓛^d`-a.e., then MCRPS (5) and
MCRPS′ (6) are strictly proper on the class of all probability distributions on `ℝ^d`. -/
theorem mcrps_strictly_proper {d : ℕ} (h : E d → ℝ) (hh : Measurable h)
    (h_nonneg : ∀ z, 0 ≤ h z) (h_int : Integrable h) (h_ne : ∀ᵐ z, h z ≠ 0)
    (PX PY : Measure (E d)) [IsProbabilityMeasure PX] [IsProbabilityMeasure PY]
    (hne : PX ≠ PY) :
    (∫ y, MCRPS PY h y ∂PY) < (∫ y, MCRPS PX h y ∂PY) ∧
      (∫ y, MCRPS' PY h y ∂PY) < (∫ y, MCRPS' PX h y ∂PY) := by sorry

end MultivarScores.L2Rule
