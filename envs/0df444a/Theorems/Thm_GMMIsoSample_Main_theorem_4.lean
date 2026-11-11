-- Prove2me | Theorems.Thm_GMMIsoSample_Main_theorem_4
-- name    : GMMIsoSample.Main.theorem_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:33:25.937128+00:00
-- url     : https://prove2.me/theorems/2481d009-c2b9-426f-a5e2-a0a66d582f7c
-- title:
--   Theorem 4 — ExactClustering on NEC samples performs exact clustering w.p. ≥ 1 − 1/d³ in the key range
-- statement:
--   Read CountClusters as in finding I1 (amplification constant $A$). There are $A>0$ and a polynomial $P$ such that for all $k_{\max}\ge1$ and $w_{\min}>0$ there is a polylogarithmic threshold $c_0(\log d)^{a_0}$ ($c_0>0$, $a_0\ge0$) with the following property for all sufficiently large $d$ and every $\Gamma_0$ with
--   $$c_0(\log d)^{a_0}\le\Gamma_0\le d^{1/4}.$$
--   Let $D$ be a mixture of $k\le k_{\max}$ spherical Gaussians with weights $\ge w_{\min}$ and normalized minimum separation $\ge\Gamma_0$, and let $X$ be $N_{EC}=2\lceil P(k_{\max},1/w_{\min})(d/\Gamma_0^4)(\log d)^{20}\rceil$ i.i.d. draws from $D$. Then ExactClustering$(k_{\max},w_{\min},\Gamma_0,X)$ partitions the sample points into $k$ nonempty groups that are exactly the true components' points, with failure probability at most $1/d^3$, whichever optimal SDP solutions it uses.
--
--   This is the paper's central technical result: exact clustering with $\tilde O(d/\Gamma_0^4)$ points, sublinear in $d$ in the key range.
--
--   Differences from the source:
--
--   - reading: CountClusters in Step 2 of ExactClustering (undefined) → the amplified-majority CountClusters with an existentially quantified constant A > 0; reason: finding I1
--   - reading: 'Fix kmax, wmin. There is a polynomial P' → one polynomial P ∈ ℝ[x, y] for all kmax, wmin, evaluated at (kmax, 1/wmin); reason: of the two readings this is the stronger and the one (55) gives (P = 12 C kmax²/wmin³)
--   - reading: polylog(d) ≤ Γ0 → c₀ (log d)^{a₀} ≤ Γ0 for some c₀ > 0, a₀ ≥ 0 depending on kmax, wmin; reason: the proof pins the endpoint (56), Γ0² ≥ 16C²kmax² log d/wmin², which is of this form
--   - reading: ExactClustering's free choices (SDP optimizers, relabelling in Step 4) → the statement holds for every output the algorithm can produce; the output is the set of blocks, so relabelling is immaterial; reason: the paper leaves these choices free
--   - encoding: i.i.d. sample points from D together with their (unobserved) component labels → an i.i.d. sample from labeledMix p, the joint law of (label, point); reason: the points' marginal is D; the labels define the true clustering the statement refers to
--   - encoding: target D = Mix(μ̄, σ̄, w̄), components indexed by [k] → a parameter tuple p : Fin k → ℝ × ℝ × ℝ^d (0-based) with mix p = Σ w_i N(μ_i, σ_i² I_d); reason: the paper itself parametrizes targets by these tuples; Γ(D) ≥ Γ is the pairwise condition over i ≠ j
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 6 (restated p. 34), Theorem 4

import Mathlib
import Definitions.Def_GMMIsoSample_Main_Model
import Definitions.Def_GMMIsoSample_Main_Clustering

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Theorem 4 (p. 6), with CountClusters read with an amplification constant `A` (finding I1):
there are `A > 0` and a polynomial `P` (in `kmax` and `1/wmin`) such that for all `kmax ≥ 1`,
`wmin > 0`, for some polylogarithmic threshold `c₀ (log d)^{a₀}`, for all sufficiently large `d`
and every `Γ₀` with `c₀ (log d)^{a₀} ≤ Γ₀ ≤ d^{1/4}`: for every target `D` (`k ≤ kmax` components,
weights `≥ wmin`, `Γ(D) ≥ Γ₀`) and `NEC = 2⌈P(kmax, 1/wmin) (d/Γ₀⁴)(log d)^20⌉` i.i.d. draws,
ExactClustering(kmax, wmin, Γ₀, X) partitions the sample into `k` nonempty groups that are
exactly the true components' points, with failure probability at most `1/d³`, whichever optimal
SDP solutions it uses. -/
theorem theorem_4 :
    ∃ A : ℝ, 0 < A ∧ ∃ P : MvPolynomial (Fin 2) ℝ, ∀ (kmax : ℕ) (wmin : ℝ), 1 ≤ kmax → 0 < wmin →
      ∃ c₀ a₀ : ℝ, 0 < c₀ ∧ 0 ≤ a₀ ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
        ∀ Γ₀ : ℝ, c₀ * Real.log d ^ a₀ ≤ Γ₀ → Γ₀ ≤ (d : ℝ) ^ (1 / 4 : ℝ) →
        ∀ (k : ℕ) (p : Params d k), IsTarget kmax wmin Γ₀ p →
          iidLaw (labeledMix p) (nEC (MvPolynomial.eval ![(kmax : ℝ), 1 / wmin] P) d Γ₀)
            {x | ∃ o ∈ exactClusteringOutputs A kmax wmin Γ₀ (fun t => (x t).2),
              ¬ IsExactClustering (fun t => (x t).1) o} ≤
            ENNReal.ofReal (1 / (d : ℝ) ^ 3) := by sorry

end GMMIsoSample.Main
