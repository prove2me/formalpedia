-- Prove2me | Theorems.Thm_GMMIsoSample_Main_theorem_20
-- name    : GMMIsoSample.Main.theorem_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:33:13.352757+00:00
-- url     : https://prove2.me/theorems/ccf4a9f1-a66a-4b6f-bb77-11b7b422a9af
-- title:
--   Theorem 20 — RadiusGrouping returns whole τ-compatible radius groups with scale estimates, w.p. ≥ 1 − 1/(10d³)
-- statement:
--   Fix $k_{\max}\ge1$, $w_{\min}>0$ and a constant $C\ge1$ (in the paper, $C$ is at least the constants of Theorems 21 and 22). Let $N=N_{EC}$ with $P(k_{\max},1/w_{\min})=12Ck_{\max}^2/w_{\min}^3$ (55), $\tau=(\log d)^{11}/\sqrt d$ (53), and let $\Gamma_0>0$ satisfy $\Gamma_0^2\ge16C^2k_{\max}^2\log d/w_{\min}^2$ (56) and $\Gamma_0\le d^{1/4}$. Then for all sufficiently large $d$ and every target $D$ with $k\le k_{\max}$ components, weights $\ge w_{\min}$ and $\Gamma(D)\ge\Gamma_0$, with probability at least
--   $$1-\frac1{10d^3}$$
--   over $N$ i.i.d. draws from $D$, RadiusGrouping returns $H\le k$ pairs $(C_1,\hat s_1),\dots,(C_H,\hat s_H)$ where $C_1\sqcup\dots\sqcup C_H$ partitions the sample into nonempty sets, and there is a partition $[k]=I_1\sqcup\dots\sqcup I_H$ into nonempty sets such that every $I_i$ is $\tau$-compatible, $C_i$ contains exactly the points drawn from components in $I_i$, and $\hat s_i^2$ is an integer power of $1+\tau$ with $1\le\sigma_j^2/\hat s_i^2\le1+3\tau$ for every $j\in I_i$.
--
--   This is the first module of ExactClustering: it splits the components into groups of nearly equal radius without knowing them.
--
--   Differences from the source:
--
--   - generalization: N = NEC with the polynomial P of (55) for the constant C of Theorems 21–22 (some C ≥ 1) → every constant C ≥ 1, with P = 12 C kmax²/wmin³ and the lower endpoint (56) for that C; reason: the source's choice is one such C, so the statement specializes to it; the proof (Lemma 25) uses only the size of N
--   - reading: the standing setting of §5 (sufficiently large d, Γ0 in the key range, Γ(D) ≥ Γ0) → ∃ d₀ (depending on kmax, wmin, C); Γ0 > 0 with (56) and Γ0 ≤ d^{1/4}; IsTarget kmax wmin Γ0; reason: Theorem 20 sits inside the proof of Theorem 4, whose key range has lower endpoint (56)
--   - encoding: ŝ_i → the output stores ŝ_i² (the paper's statement is about ŝ_i²); reason: no instance changes
--   - encoding: i.i.d. sample points from D together with their (unobserved) component labels → an i.i.d. sample from labeledMix p, the joint law of (label, point); reason: the points' marginal is D; the labels define the true clustering the statement refers to
--   - encoding: target D = Mix(μ̄, σ̄, w̄), components indexed by [k] → a parameter tuple p : Fin k → ℝ × ℝ × ℝ^d (0-based) with mix p = Σ w_i N(μ_i, σ_i² I_d); reason: the paper itself parametrizes targets by these tuples; Γ(D) ≥ Γ is the pairwise condition over i ≠ j
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 36 (restated p. 39), Theorem 20; setting of p. 38, (55)–(56)

import Mathlib
import Definitions.Def_GMMIsoSample_Main_Model
import Definitions.Def_GMMIsoSample_Main_Clustering

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Theorem 20 (p. 36), in the setting of Theorem 4's proof: `NEC` with
`P(kmax, 1/wmin) = 12 C kmax²/wmin³` (55), `Γ₀² ≥ 16 C² kmax² log d / wmin²` (56), `Γ₀ ≤ d^{1/4}`,
for every constant `C ≥ 1`. For all sufficiently large `d`, with probability at least
`1 − 1/(10d³)` over `N = NEC` i.i.d. draws from a target `D` (`k ≤ kmax` components, weights
`≥ wmin`, `Γ(D) ≥ Γ₀`), RadiusGrouping returns `H ≤ k` pairs `(C_h, ŝ_h)` with the `C_h` a
partition of the sample into nonempty sets, and some partition `[k] = I₁ ⊔ ⋯ ⊔ I_H` into nonempty
`τ`-compatible sets (`τ = (log d)^11/√d`) has `C_h` = the points drawn from the components in
`I_h` and `ŝ_h²` an integer power of `1 + τ` with `1 ≤ σ_j²/ŝ_h² ≤ 1 + 3τ` for `j ∈ I_h`. -/
theorem theorem_20 :
    ∀ (kmax : ℕ) (wmin : ℝ), 1 ≤ kmax → 0 < wmin → ∀ C : ℝ, 1 ≤ C →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ Γ₀ : ℝ, 0 < Γ₀ →
        16 * C ^ 2 * kmax ^ 2 * Real.log d / wmin ^ 2 ≤ Γ₀ ^ 2 → Γ₀ ≤ (d : ℝ) ^ (1 / 4 : ℝ) →
        ∀ (k : ℕ) (p : Params d k), IsTarget kmax wmin Γ₀ p →
          iidLaw (labeledMix p) (nEC (12 * C * kmax ^ 2 / wmin ^ 3) d Γ₀)
            {x | ¬ RadiusGroupingGood p (tauD d) (fun t => (x t).1)
              (radiusGrouping (fun t => (x t).2))} ≤ ENNReal.ofReal (1 / (10 * (d : ℝ) ^ 3)) := by sorry

end GMMIsoSample.Main
