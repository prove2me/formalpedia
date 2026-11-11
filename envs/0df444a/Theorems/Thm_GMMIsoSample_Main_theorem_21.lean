-- Prove2me | Theorems.Thm_GMMIsoSample_Main_theorem_21
-- name    : GMMIsoSample.Main.theorem_21
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:33:01.027209+00:00
-- url     : https://prove2.me/theorems/6286fcb7-84f2-40eb-b5b8-aa634a943b57
-- title:
--   Theorem 21 — CountClusters returns |I| on m samples from a τ-compatible D_I, w.p. ≥ 1 − d⁻⁴
-- statement:
--   Read CountClusters as in finding I1: divide the points by $\hat s$, split them into $\lceil A\log d\rceil$ consecutive blocks, run CountClusters\* on each and take the most frequent answer. There are constants $A>0$ and $C>0$ such that the following holds for every $k_{\max}\ge1$, $w_{\min}>0$ and all sufficiently large $d$. Let $\rho=3\tau$, $\tau=(\log d)^{11}/\sqrt d$. If $w_{\min}\Gamma_0\ge Ck_{\max}$ and
--   $$m\ge C\max\Big(\frac{dk_{\max}^2}{w_{\min}^2\Gamma_0^4},\frac{k_{\max}}{w_{\min}},\frac{\rho dk_{\max}}{w_{\min}\Gamma_0^2}\Big)\log d,$$
--   then for every target $D$ ($k\le k_{\max}$ components, weights $\ge w_{\min}$, $\Gamma(D)\ge\Gamma_0$), every $\tau$-compatible $I\subseteq[k]$ and every $\hat s>0$ with $1\le\sigma_j^2/\hat s^2\le1+\rho$ for $j\in I$ (54), CountClusters given $\hat s$ and $m$ independent examples from $D_I$ returns $|I|$ with probability at least $1-d^{-4}$.
--
--   This is the second module of ExactClustering; ClusterRadiusGroup needs the exact number of components of each radius group.
--
--   Differences from the source:
--
--   - reading: CountClusters (never defined; Theorem 21 'follows by standard amplifications' of CountClusters*, Theorem 30) → majority vote of CountClusters* on max(1, ⌈A log d⌉) consecutive blocks of the points divided by ŝ, with an existentially quantified amplification constant A > 0; reason: finding I1: the log d factor in m indicates about log d independent blocks and a vote; the constant of the amplification is part of the existential claim
--   - reading: the standing setting of §5 (D with k ≤ kmax, weights ≥ wmin, Γ(D) ≥ Γ0; sufficiently large d) → IsTarget kmax wmin Γ0 p and ∃ d₀ depending on kmax, wmin; C absolute; reason: the constant C enters P(kmax, 1/wmin) = 12 C kmax²/wmin³ (55), so it does not depend on kmax, wmin
--   - generalization: Γ0 in the key range polylog(d) ≤ Γ0 ≤ d^{1/4} (§5 setting) → any Γ0 > 0 with wmin Γ0 ≥ C kmax; reason: Theorem 21's own hypotheses and the conditions 1–3 of §7 do not use the key range; the statement specializes to it
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), pp. 36–37 (restated p. 46), Theorem 21

import Mathlib
import Definitions.Def_GMMIsoSample_Main_Model
import Definitions.Def_GMMIsoSample_Main_Clustering

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Theorem 21 (pp. 36–37), with CountClusters read as the majority vote of CountClusters* over
`⌈A log d⌉` blocks (finding I1): there are constants `A > 0` and `C > 0` such that for all
sufficiently large `d`, if `wmin Γ₀ ≥ C kmax` and
`m ≥ C max(d kmax²/(wmin² Γ₀⁴), kmax/wmin, ρ d kmax/(wmin Γ₀²)) log d` (`ρ = 3τ`), then for every
target `D` (`k ≤ kmax`, weights `≥ wmin`, `Γ(D) ≥ Γ₀`), every `τ`-compatible `I ⊆ [k]` and every
`ŝ > 0` with `1 ≤ σ_j²/ŝ² ≤ 1 + ρ` for `j ∈ I` (54), CountClusters on `ŝ` and `m` independent
examples from `D_I` returns `|I|` with probability at least `1 − d^{−4}`. -/
theorem theorem_21 :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧ ∀ (kmax : ℕ) (wmin : ℝ), 1 ≤ kmax → 0 < wmin →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ Γ₀ : ℝ, 0 < Γ₀ → C * kmax ≤ wmin * Γ₀ →
        ∀ m : ℕ, C * max (max ((d : ℝ) * kmax ^ 2 / (wmin ^ 2 * Γ₀ ^ 4)) ((kmax : ℝ) / wmin))
            (3 * tauD d * d * kmax / (wmin * Γ₀ ^ 2)) * Real.log d ≤ m →
        ∀ (k : ℕ) (p : Params d k), IsTarget kmax wmin Γ₀ p →
        ∀ I : Finset (Fin k), IsTauCompatible p I (tauD d) →
        ∀ s : ℝ, 0 < s →
          (∀ j ∈ I, 1 ≤ rad p j ^ 2 / s ^ 2 ∧ rad p j ^ 2 / s ^ 2 ≤ 1 + 3 * tauD d) →
          iidLaw (condMix p I) m {x | countClusters A kmax wmin Γ₀ s x ≠ I.card} ≤
            ENNReal.ofReal ((d : ℝ) ^ (-4 : ℝ)) := by sorry

end GMMIsoSample.Main
