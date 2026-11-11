-- Prove2me | Theorems.Thm_GMMIsoSample_Main_theorem_22
-- name    : GMMIsoSample.Main.theorem_22
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:33:00.774609+00:00
-- url     : https://prove2.me/theorems/a6afbfce-1a71-4139-a4ff-8d2f58c7da77
-- title:
--   Theorem 22 — ClusterRadiusGroup (the q-means SDP) recovers the true clustering, w.p. ≥ 1 − d⁻⁴
-- statement:
--   There is a constant $C>0$ such that for every $k_{\max}\ge1$, $w_{\min}>0$ and all sufficiently large $d$: if $m\ge1$,
--   $$w_{\min}\Gamma_0\ge Ck_{\max}\sqrt{\log(k_{\max}dm)}\quad\text{and}\quad m\ge C\max\Big(\frac{dk_{\max}^2}{w_{\min}^2\Gamma_0^4},\frac{k_{\max}}{w_{\min}},\frac{\rho dk_{\max}}{w_{\min}\Gamma_0^2}\Big)\log(k_{\max}dm)$$
--   ($\rho=3\tau$, $\tau=(\log d)^{11}/\sqrt d$), then for every target $D$ ($k\le k_{\max}$, weights $\ge w_{\min}$, $\Gamma(D)\ge\Gamma_0$) and every $\tau$-compatible $I\subseteq[k]$, ClusterRadiusGroup given $m$ independent examples from $D_I$ and the number $|I|$ outputs the correct clustering of the $m$ examples (their partition by generating component) with probability at least $1-d^{-4}$ — whichever optimal solution of the SDP (81) it uses.
--
--   This is the third module of ExactClustering: an SDP relaxation of $q$-means clustering that is exact on a radius group.
--
--   Differences from the source:
--
--   - reading: the standing setting of §5 (D with k ≤ kmax, weights ≥ wmin, Γ(D) ≥ Γ0; sufficiently large d) → IsTarget kmax wmin Γ0 p and ∃ d₀ depending on kmax, wmin; C absolute; reason: C enters (55) as an absolute constant
--   - generalization: Γ0 in the key range (§5 setting) → any Γ0 > 0 satisfying the theorem's two conditions; reason: Theorem 22's hypotheses do not involve the key range; the statement specializes to it
--   - reading: 'an optimal solution Ẑ' of (81) → every optimal solution (all outputs of crgOutputs); failure if (81) has none; reason: the paper leaves the choice of optimizer free, so the guarantee must hold for each
--   - encoding: m examples with log(kmax d m) in the hypotheses → hypothesis 1 ≤ m; reason: log(kmax d m) is undefined for m = 0 (Lean's log 0 = 0 would admit an empty sample)
--   - encoding: i.i.d. sample points from D together with their (unobserved) component labels → an i.i.d. sample from labeledMix p, the joint law of (label, point); reason: the points' marginal is D; the labels define the true clustering the statement refers to
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 37 (restated pp. 54–55), Theorem 22

import Mathlib
import Definitions.Def_GMMIsoSample_Main_Model
import Definitions.Def_GMMIsoSample_Main_Clustering

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Theorem 22 (p. 37): there is a constant `C > 0` such that for all sufficiently large `d`, if
`wmin Γ₀ ≥ C kmax √(log(kmax d m))` and
`m ≥ C max(d kmax²/(wmin² Γ₀⁴), kmax/wmin, ρ d kmax/(wmin Γ₀²)) log(kmax d m)` (`ρ = 3τ`), then for
every target `D` (`k ≤ kmax`, weights `≥ wmin`, `Γ(D) ≥ Γ₀`) and every `τ`-compatible `I ⊆ [k]`,
ClusterRadiusGroup on `m ≥ 1` independent examples from `D_I` and `q = |I|` outputs the correct
clustering of the examples (their partition by generating component) with probability at least
`1 − d^{−4}`, whichever optimal solution of the SDP (81) it uses. -/
theorem theorem_22 :
    ∃ C : ℝ, 0 < C ∧ ∀ (kmax : ℕ) (wmin : ℝ), 1 ≤ kmax → 0 < wmin →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ Γ₀ : ℝ, 0 < Γ₀ → ∀ m : ℕ, 1 ≤ m →
        C * kmax * Real.sqrt (Real.log ((kmax : ℝ) * d * m)) ≤ wmin * Γ₀ →
        C * max (max ((d : ℝ) * kmax ^ 2 / (wmin ^ 2 * Γ₀ ^ 4)) ((kmax : ℝ) / wmin))
            (3 * tauD d * d * kmax / (wmin * Γ₀ ^ 2)) * Real.log ((kmax : ℝ) * d * m) ≤ m →
        ∀ (k : ℕ) (p : Params d k), IsTarget kmax wmin Γ₀ p →
        ∀ I : Finset (Fin k), IsTauCompatible p I (tauD d) →
          iidLaw (condLabeledMix p I) m
            {x | ∃ o ∈ crgOutputs (fun t => (x t).2) I.card,
              o ≠ some (trueBlocks (fun t => (x t).1))} ≤
            ENNReal.ofReal ((d : ℝ) ^ (-4 : ℝ)) := by sorry

end GMMIsoSample.Main
