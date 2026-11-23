-- Prove2me | Theorems.Thm_OptInapprox_Bal2Sat_Supplement_theorem_5
-- name    : OptInapprox.Bal2Sat.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:57:50.467614+00:00
-- url     : https://prove2.me/theorems/d24502d8-4117-4521-a090-8538bd48385c
-- title:
--   Theorem 5 — balanced threshold functions are as noise-stable as Majority, up to O(δ(1−|ρ|)^{−3/2})
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $a\in\mathbb R^n$ be such that $a_1x_1+\cdots+a_nx_n\ne0$ for every $x\in\{-1,1\}^n$, and let $f(x)=\operatorname{sgn}(a_1x_1+\cdots+a_nx_n)$. If $\operatorname{Inf}_i(f)\le\delta$ for every $i$, then for every $\rho\in[-1,1]$
--
--   $$\Bigl|\mathbb S_\rho(f)-\Bigl(1-\tfrac2\pi\arccos\rho\Bigr)\Bigr|\,(1-|\rho|)^{3/2}\le C\,\delta,$$
--
--   that is, $\mathbb S_\rho(f)=1-\frac2\pi\arccos\rho\pm O(\delta(1-|\rho|)^{-3/2})$. Noise stability and influences are the published Boolean ones (Definitions 2 and 3). The result says every regular balanced threshold function has asymptotically the noise stability of Majority.
--
--   Differences from the source:
--   - reading: ±O(δ(1−|ρ|)^{−3/2}) → one absolute constant C>0, chosen before n, a, δ and ρ, with the bound multiplied through by (1−|ρ|)^{3/2}; reason: uniform reading of O(·); at ρ=±1 the printed bound is infinite and the multiplied form is 0 ≤ Cδ, equivalent
--   - encoding: δ = max_i Inf_i(f) → every δ with Inf_i(f) ≤ δ for all i; reason: the bound is increasing in δ, so this is equivalent to δ equal to the maximum
--   - encoding: balanced threshold function sgn(a·x) → thresholdFn a with the hypothesis that a·x ≠ 0 on the whole cube; reason: footnote 1, p. 22: the linear form is assumed never to vanish, so sgn takes values ±1
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 12, Theorem 5; footnote 1, p. 22; proof §10, pp. 22–24

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Supplement_Threshold

namespace OptInapprox.Bal2Sat.Supplement

theorem theorem_5 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (a : Fin n → ℝ),
      (∀ x : Fin n → Bool, ∑ i, a i * OptInapprox.MaxCut.pm (x i) ≠ 0) →
      ∀ δ : ℝ, (∀ i, OptInapprox.MaxCut.influence i (thresholdFn a) ≤ δ) →
      ∀ ρ : ℝ, -1 ≤ ρ → ρ ≤ 1 →
        |OptInapprox.MaxCut.noiseStab ρ (thresholdFn a) -
            (1 - 2 / Real.pi * Real.arccos ρ)| * (1 - |ρ|) ^ ((3 : ℝ) / 2) ≤ C * δ := by sorry

end OptInapprox.Bal2Sat.Supplement
