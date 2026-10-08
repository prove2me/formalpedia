-- Prove2me | Theorems.Thm_OptInapprox_MaxCut_proposition_7_3
-- name    : OptInapprox.MaxCut.proposition_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:28:00.353695+00:00
-- url     : https://prove2.me/theorems/460b99cd-470c-4295-ae3c-55e07825ee5d
-- title:
--   Proposition 7.3, p. 17 — Majority Is Stablest with low-degree influences
-- statement:
--   Assume the Majority Is Stablest theorem. Fix $\rho\in[0,1)$ and $\epsilon>0$. Then there are $\delta'>0$ and $k'\in\mathbb N$, depending only on $\epsilon$ and $\rho$, such that every $f:\{-1,1\}^n\to[-1,1]$ with $\mathbf E[f]=0$ and $\mathrm{Inf}_i^{\le k'}(f)\le\delta'$ for all $i$ satisfies
--   $$\mathbb S_\rho(f)\le 1-\tfrac{2}{\pi}\arccos\rho+\epsilon.$$
--
--   That is, Majority Is Stablest remains true when the small-influence hypothesis is replaced by a small *low-degree* influence hypothesis, which is the form a list-decoding argument can use.
--
--   **Formalization Note.** The Majority Is Stablest theorem, which the paper cites from [45], enters as the hypothesis `MajorityIsStablest`. $\delta'$ and $k'$ are chosen before $n$ and $f$.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 17, Proposition 7.3

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_MIS

namespace OptInapprox.MaxCut

theorem proposition_7_3 (hMIS : MajorityIsStablest) (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∃ k' : ℕ,
      ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ), (∀ x, |f x| ≤ 1) → cubeE f = 0 →
        (∀ i, lowDegInf k' i f ≤ δ') → noiseStab ρ f ≤ 1 - 2 / Real.pi * Real.arccos ρ + ε := by sorry

end OptInapprox.MaxCut
