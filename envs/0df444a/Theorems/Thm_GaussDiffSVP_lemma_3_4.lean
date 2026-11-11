-- Prove2me | Theorems.Thm_GaussDiffSVP_lemma_3_4
-- name    : GaussDiffSVP.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:59:01.014565+00:00
-- url     : https://prove2.me/theorems/38dec57f-8629-4ff4-84c8-71bcdf213a75
-- title:
--   Lemma 3.4 — $\#\{x\in L:\|x\|\le R\lambda_1(L)\}\le C_{R_0}(n+1)2^{0.401n}R^n$
-- statement:
--   Write $\beta_{KL} = 2^{\kappa_{\mathrm{pack}}} = 2^{0.401}$. For every fixed $R_0\ge1$ there are constants $C_{R_0}$ and $n_{R_0}$ such that for every $n\ge n_{R_0}$, every full-rank lattice $L\subset\mathbb R^n$ and simultaneously all $1\le R\le R_0$,
--   $$\#\{x\in L : \|x\|\le R\lambda_1(L)\}\le C_{R_0}(n+1)\,\beta_{KL}^n R^n .$$
--   It is the bounded-radius lattice form of the Kabatiansky–Levenshtein spherical-code bound; it controls terminal representations and dual Gaussian mass.
--
--   Differences from the source:
--   - encoding: full-rank lattice $L$; the count → $L = B\mathbb Z^n$ with $\det B\ne0$; the count (including $x=0$) as a cardinal in $[0,\infty]$; reason: same instances
--   - encoding: $\beta_{KL}^n$ → $2^{(401/1000)n}$; reason: $\beta_{KL} = 2^{0.401}$
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Lemma 3.4, p.21

import Mathlib
import Definitions.Def_SuperlatSVP_lat

open SuperlatSVP
open scoped ENNReal

namespace GaussDiffSVP

/-- Lemma 3.4 (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.21). Write `β_KL = 2^{κ_pack} = 2^{0.401}`. For every fixed `R₀ ≥ 1` there are
constants `C_{R₀}` and `n_{R₀}` such that, for every `n ≥ n_{R₀}` and every full-rank lattice
`L ⊂ ℝⁿ`, simultaneously for all `1 ≤ R ≤ R₀`,
`#{x ∈ L : ‖x‖ ≤ Rλ₁(L)} ≤ C_{R₀}(n + 1) β_KLⁿ Rⁿ`.

**Formalization Note.** `L = Bℤⁿ` with `B.det ≠ 0`; `λ₁` is `SuperlatSVP.lam1`; the count includes
`x = 0` and is `Set.encard` (compared in `ℝ≥0∞`); `β_KLⁿ = 2^{(401/1000)n}`. -/
theorem lemma_3_4 :
    ∀ R₀ : ℝ, 1 ≤ R₀ → ∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 → ∀ R : ℝ, 1 ≤ R → R ≤ R₀ →
        (({x : E n | x ∈ lat B ∧ ‖x‖ ≤ R * lam1 (lat B)}.encard : ℕ∞) : ℝ≥0∞) ≤
          ENNReal.ofReal (C * ((n : ℝ) + 1) * (2 : ℝ) ^ ((401 / 1000 : ℝ) * n) * R ^ n) := by sorry

end GaussDiffSVP
