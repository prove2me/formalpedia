-- Prove2me | Theorems.Thm_OptInapprox_MaxCut_proposition_7_4
-- name    : OptInapprox.MaxCut.proposition_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:28:08.623982+00:00
-- url     : https://prove2.me/theorems/1d31a71e-27ee-4479-af16-58fd6cc14fb8
-- title:
--   Proposition 7.4, p. 17 — Majority Is Stablest 'in reverse' for ρ ∈ (−1, 0], without E[f] = 0
-- statement:
--   Assume the Majority Is Stablest theorem. Fix $\rho\in(-1,0]$ and $\epsilon>0$. Then there is $\delta>0$ such that every $f:\{-1,1\}^n\to[-1,1]$ with $\mathrm{Inf}_i(f)\le\delta$ for all $i$ satisfies
--   $$\mathbb S_\rho(f)\ge1-\tfrac{2}{\pi}\arccos\rho-\epsilon.$$
--   No assumption on $\mathbf E[f]$ is needed.
--
--   For negative correlation the inequality reverses: functions with small influences cannot be much more *anti*-stable than majority.
--
--   **Formalization Note.** The Majority Is Stablest theorem, which the paper cites from [45], enters as the hypothesis `MajorityIsStablest`. $\delta$ is chosen before $n$ and $f$.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 17, Proposition 7.4

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_MIS

namespace OptInapprox.MaxCut

theorem proposition_7_4 (hMIS : MajorityIsStablest) (ρ : ℝ) (hρ₀ : -1 < ρ) (hρ₁ : ρ ≤ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ), (∀ x, |f x| ≤ 1) →
        (∀ i, influence i f ≤ δ) → 1 - 2 / Real.pi * Real.arccos ρ - ε ≤ noiseStab ρ f := by sorry

end OptInapprox.MaxCut
