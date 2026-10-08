-- Prove2me | Theorems.Thm_OptInapprox_MaxCut_proposition_7_5
-- name    : OptInapprox.MaxCut.proposition_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:28:04.279261+00:00
-- url     : https://prove2.me/theorems/e7d20748-203f-44ab-8f82-bc9fa1dec0eb
-- title:
--   Proposition 7.5, p. 18 — for ρ ∈ (−1, 0], small low-degree influences give 𝕊_ρ(f) ≥ 1 − (2/π) arccos ρ − ε
-- statement:
--   Assume the Majority Is Stablest theorem. Fix $\rho\in(-1,0]$. Then for any $\epsilon>0$ there are a small enough $\delta=\delta(\epsilon,\rho)>0$ and a large enough $k=k(\epsilon,\rho)$ such that every $f:\{-1,1\}^n\to[-1,1]$ with $\mathrm{Inf}_i^{\le k}(f)\le\delta$ for all $i=1,\dots,n$ satisfies
--   $$\mathbb S_\rho(f)\ge1-\tfrac{2}{\pi}\arccos\rho-\epsilon.$$
--
--   This is the form of Majority Is Stablest used in the soundness analysis of the MAX-CUT verifier.
--
--   **Formalization Note.** The Majority Is Stablest theorem, which the paper cites from [45], enters as the hypothesis `MajorityIsStablest`. $\delta$ and $k$ are chosen before $n$ and $f$.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 18, Proposition 7.5

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_MIS

namespace OptInapprox.MaxCut

theorem proposition_7_5 (hMIS : MajorityIsStablest) (ρ : ℝ) (hρ₀ : -1 < ρ) (hρ₁ : ρ ≤ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ k : ℕ,
      ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ), (∀ x, |f x| ≤ 1) →
        (∀ i, lowDegInf k i f ≤ δ) → 1 - 2 / Real.pi * Real.arccos ρ - ε ≤ noiseStab ρ f := by sorry

end OptInapprox.MaxCut
