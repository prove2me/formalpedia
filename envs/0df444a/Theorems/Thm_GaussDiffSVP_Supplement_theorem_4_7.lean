-- Prove2me | Theorems.Thm_GaussDiffSVP_Supplement_theorem_4_7
-- name    : GaussDiffSVP.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:48:12.812798+00:00
-- url     : https://prove2.me/theorems/dc33e794-338b-4a03-9682-aab0c2db35cc
-- title:
--   Theorem 4.7 — weighted readout from $\mathcal C_H(\nu,\varepsilon)$: $d_{TV}\le 1-e^{-3\varepsilon}M/(M+1)$
-- statement:
--   Let $\Xi=(X_i)$ be a finite random record list on a countable space $\mathcal X$ in the class $\mathcal C_H(\nu,\varepsilon)$: given the retained information $H$, its intensity satisfies $e^{-\varepsilon}\nu\le m_\Xi\le e^{\varepsilon}\nu$ and its second factorial measure $S_\Xi\le e^{\varepsilon}\nu^{\otimes2}$. Let $b:\mathcal X\to[0,1]$ be an $H$-measurable weight and put
--   $$0<M=\nu(b)<\infty,\qquad W=\sum_i b(X_i),\qquad \pi_H=\frac{b\nu}{M}.$$
--   Choose record $i$ with probability $b(X_i)/W$ when $W>0$, and return a fixed fallback point when $W=0$. Then, almost surely,
--   $$d_{TV}\big(\mathcal L(X_{\mathrm{out}}\mid H),\pi_H\big)\le 1-e^{-3\varepsilon}\frac{M}{M+1}\le 3\varepsilon+\frac1{M+1},\tag{36}$$
--   $$\Pr[W=0\mid H]\le 1-e^{-3\varepsilon}\frac{M}{M+1}.\tag{37}$$
--
--   This turns factorial moment bounds on a correlated list into a sampling guarantee, with error linear in the moment distortion and in the inverse effective mass.
--
--   **Formalization Note** The statement is made for each conditional law $\mu$ of the list given $H$, with the $H$-measurable data $\nu,\varepsilon,b,x_0$ fixed; $\mathcal C(\nu,\varepsilon)$ is the published InClassC. $\nu(b)=\sum_x b(x)\nu(x)$ is computed in $[0,\infty]$ and $M$ is its real value.
--
--   Differences from the source:
--   - encoding: conditional statements given H, almost surely → the statement for every conditional law μ of the list given H, with the H-measurable data fixed; reason: the convention of the published InClassC: one law per value of H
--   - encoding: records with distinct IDs → list positions; reason: as in the published intensity and factMoment
--   - encoding: d_TV(·,·) and ν(b) → ½Σₓ((p−π)+(π−p)) with truncated subtraction in ℝ≥0∞, and ν(b) = Σₓ b(x)ν(x) in ℝ≥0∞ with M its real value; reason: same quantities; truncated subtraction makes the sum equal Σ|p−π|
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Theorem 4.7, p.26 ((36)–(37), p.26; Definition 4.2, p.23)

import Mathlib
import Definitions.Def_GaussDiffSVP_InClassC
import Definitions.Def_GaussDiffSVP_Supplement_Readout

open scoped ENNReal

namespace GaussDiffSVP.Supplement

/-- Theorem 4.7 (Weighted readout) (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.26). Let `Ξ ∈ C_H(ν, ε)` be finite. For an
`H`-measurable weight `b : X → [0, 1]`, put `0 < M = ν(b) < ∞`, `W = Σᵢ b(Xᵢ)`, `π_H = bν/M`.
Choose record `i` with probability `b(Xᵢ)/W` when `W > 0`, and return a fixed fallback point when
`W = 0`. Then, almost surely,
`d_TV(L(X_out | H), π_H) ≤ 1 − e^{−3ε} M/(M + 1) ≤ 3ε + 1/(M + 1)` (36) and
`P[W = 0 | H] ≤ 1 − e^{−3ε} M/(M + 1)` (37).

**Formalization Note.** The retained information `H` is fixed: `μ` is the conditional law of the
(finite) record list given `H`, and `b`, `x₀`, `ν`, `ε` are its `H`-measurable data; the statement
for every such law is the "almost surely" statement. `C(ν, ε)` is the published
`GaussDiffSVP.InClassC` (it includes `ε ≥ 0`); `ν(b) = Σₓ b(x)ν(x)` in `ℝ≥0∞`, `M` its real value.
`d_TV` is `½ Σₓ |p(x) − π(x)|` on the countable space `X` (written with truncated subtraction in
`ℝ≥0∞`). -/
theorem theorem_4_7 {α : Type*} [Countable α] (μ : PMF (List α)) (ν : α → ℝ≥0∞) (ε : ℝ)
    (hC : GaussDiffSVP.InClassC μ ν ε) (b : α → ℝ) (hb0 : ∀ x, 0 ≤ b x) (hb1 : ∀ x, b x ≤ 1)
    (x₀ : α) (hM0 : 0 < ∑' x, ENNReal.ofReal (b x) * ν x)
    (hMtop : ∑' x, ENNReal.ofReal (b x) * ν x < ⊤) :
    let Mt : ℝ≥0∞ := ∑' x, ENNReal.ofReal (b x) * ν x
    let M : ℝ := Mt.toReal
    let π : α → ℝ≥0∞ := fun x => ENNReal.ofReal (b x) * ν x / Mt
    (1 / 2 : ℝ≥0∞) * ∑' x, ((readoutLaw μ b x₀ x - π x) + (π x - readoutLaw μ b x₀ x)) ≤
        ENNReal.ofReal (1 - Real.exp (-3 * ε) * (M / (M + 1))) ∧
      1 - Real.exp (-3 * ε) * (M / (M + 1)) ≤ 3 * ε + 1 / (M + 1) ∧
      zeroWeightProb μ b ≤ ENNReal.ofReal (1 - Real.exp (-3 * ε) * (M / (M + 1))) := by sorry

end GaussDiffSVP.Supplement
