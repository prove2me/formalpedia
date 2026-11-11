-- Prove2me | Theorems.Thm_LpBallVI_Affine_lemma_4_7
-- name    : LpBallVI.Affine.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:11:45.18619+00:00
-- url     : https://prove2.me/theorems/d4d8d20c-d969-436b-a75b-ad639bacc6c2
-- title:
--   Lemma 4.7 — the realization N̂_{f,λ} is within 6ε Σ_j |α_j| of N_{f,λ}; auxiliary variables are bounded by 5 + 2ε + max_j(a_j S + |β_j|)
-- statement:
--   Let $1 < p < \infty$, $p \ne 2$, $\lambda > 0$, coefficients $\alpha_j, \beta_j$ and $a_j > 0$, $t \in \mathbb R$, $s_j = a_j t + \beta_j$, and $\epsilon \ge 0$. Suppose the auxiliary reals satisfy, for every $j$, the six equations $r^-_j = \sigma_\lambda(s_j - 1)$, $r^0_j = \sigma_\lambda(s_j)$, $r^+_j = \sigma_\lambda(s_j+1)$, $w^+_j = \sigma_\lambda(4 + d_j/4)$, $w^0_j = \sigma_\lambda(4)$, $w^-_j = \sigma_\lambda(4 - d_j/4)$ (with $d_j = r^+_j - 2r^0_j + r^-_j$) up to additive error $\epsilon$. Then
--   $$|\hat N_{f,\lambda}(t) - N_{f,\lambda}(t)| \le 6\epsilon \sum_{j=1}^m |\alpha_j|,$$
--   and for every $S \ge 0$ with $|t| \le S$, every auxiliary variable is at most $5 + 2\epsilon + \max_j (a_j S + |\beta_j|)$ in absolute value. This makes the affine simulation of $k_\lambda$ robust to approximate VI solutions.
--
--   Differences from the source:
--   - generalization: the rational coefficients α_j, β_j, a_j > 0 of Lemma 4.6 → real α_j, β_j and real a_j > 0; reason: the proof uses only a_j ≥ 0; the paper's coefficients are an instance
--   - reading: 'for any λ > 0 and |t| ≤ S' with S not defined in the statement → for every S ≥ 0 with |t| ≤ S; reason: the use in the proof of Lemma 4.10 with S = 2(17H + η) + 1/4
--   - encoding: max_{j∈[m]}(a_j S + |β_j|) → ⨆ over Fin m; reason: a finite supremum; for m = 0 there are no auxiliary variables
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 28, Lemma 4.7, (31)–(34)

import Mathlib
import Definitions.Def_LpBallVI_Affine_WeightedApprox

namespace LpBallVI.Affine

/-- **Lemma 4.7**, p. 28: if, for every `j ∈ [m]`, the six equations (31)–(32)
`r⁻_j = σ_λ(s_j − 1)`, `r⁰_j = σ_λ(s_j)`, `r⁺_j = σ_λ(s_j + 1)`, `w⁺_j = σ_λ(4 + d_j/4)`,
`w⁰_j = σ_λ(4)`, `w⁻_j = σ_λ(4 − d_j/4)` (`s_j = a_j t + β_j`, `d_j = r⁺_j − 2r⁰_j + r⁻_j`) hold with
additive error at most `ε ≥ 0`, then `|N̂_{f,λ}(t) − N_{f,λ}(t)| ≤ 6ε ∑_j |α_j|`; and for every
`S ≥ 0` with `|t| ≤ S`, every auxiliary variable is at most `5 + 2ε + max_j (a_j S + |β_j|)` in
absolute value. -/
theorem lemma_4_7 (p lam : ℝ) (hp : 1 < p) (hp2 : p ≠ 2) (hlam : 0 < lam) {m : ℕ}
    (α a β : Fin m → ℝ) (ha : ∀ j, 0 < a j) (t ε : ℝ) (hε : 0 ≤ ε)
    (rm r0 rp wm w0 wp : Fin m → ℝ)
    (h31m : ∀ j, |rm j - sigmaLam p lam (a j * t + β j - 1)| ≤ ε)
    (h310 : ∀ j, |r0 j - sigmaLam p lam (a j * t + β j)| ≤ ε)
    (h31p : ∀ j, |rp j - sigmaLam p lam (a j * t + β j + 1)| ≤ ε)
    (h32p : ∀ j, |wp j - sigmaLam p lam (4 + (rp j - 2 * r0 j + rm j) / 4)| ≤ ε)
    (h320 : ∀ j, |w0 j - sigmaLam p lam 4| ≤ ε)
    (h32m : ∀ j, |wm j - sigmaLam p lam (4 - (rp j - 2 * r0 j + rm j) / 4)| ≤ ε) :
    |realization p α wm w0 wp - weightedApprox p lam α a β t| ≤ 6 * ε * ∑ j, |α j| ∧
      ∀ S : ℝ, 0 ≤ S → |t| ≤ S → ∀ j, ∀ y ∈ [rm j, r0 j, rp j, wm j, w0 j, wp j],
        |y| ≤ 5 + 2 * ε + ⨆ k, (a k * S + |β k|) := by sorry

end LpBallVI.Affine
