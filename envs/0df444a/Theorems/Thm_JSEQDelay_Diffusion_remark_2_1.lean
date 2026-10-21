-- Prove2me | Theorems.Thm_JSEQDelay_Diffusion_remark_2_1
-- name    : JSEQDelay.Diffusion.remark_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:07.464697+00:00
-- url     : https://prove2.me/theorems/028c1bbf-0a05-4499-b83e-69b43c9713db
-- title:
--   Remark 2.1, p. 8 — (Q̂ⁿ_k, L̂ⁿ_k) is the Skorokhod map of Âⁿ_k − Ŝⁿ_k ∘ Bⁿ_k
-- statement:
--   Consider the $n$-th JSEQ network ($n\ge1$) and a sample path along which the arrival and service partial sums diverge. For every server $k$, the scaled idleness $\hat L^n_k(t)=\mu^n_k(t-B^n_k(t))/\sqrt n$ is non-decreasing and increases only when $\hat Q^n_k=0$, and for $t\ge0$
--   $$(\hat Q^n_k(t),\hat L^n_k(t))=\Gamma\big(\hat A^n_k-\hat S^n_k\circ B^n_k\big)(t),$$
--   where $\Gamma=(\Gamma_1,\Gamma_2)$ is the one-dimensional Skorokhod map of (72)–(73).
--
--   The remark converts the prelimit balance equation (15) into the reflection form that the proofs of Lemmas 5.2–5.3 manipulate.
--
--   **Formalization Note** "Increases only when $\hat Q^n_k=0$" is the published `StieltjesComplementary`. The statement is pathwise, on each sample path where the counts are finite.
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), p. 8, Remark 2.1

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_JSEQDelay_Diffusion_Model
import Definitions.Def_JSEQDelay_Diffusion_Skorokhod

namespace JSEQDelay.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BellWilliams2001.ThresholdPolicy RankBasedSDI.LoadBalancing

/-- **Remark 2.1** (p. 8): in the `n`-th JSEQ network, along every sample path with divergent
arrival and service partial sums and for every server `k`, the scaled idleness `L̂ⁿ_k` is
non-decreasing and increases only when `Q̂ⁿ_k = 0`, and `(Q̂ⁿ_k, L̂ⁿ_k)` is the image of
`Âⁿ_k − Ŝⁿ_k ∘ Bⁿ_k` under the one-dimensional Skorokhod map `Γ = (Γ₁, Γ₂)` of (72)–(73). -/
theorem remark_2_1 {K : ℕ} (hK : 2 ≤ K) {Ω : Type*}
    (u : ℕ → Ω → ℝ) (v : Fin K → ℕ → Ω → ℝ)
    (hu : ∀ i ω, 0 < u i ω) (hv : ∀ k i ω, 0 < v k i ω)
    (n : ℕ) (hn : 1 ≤ n) (lam : ℝ) (mu : Fin K → ℝ) (hlam : 0 < lam) (hmu : ∀ k, 0 < mu k)
    (τ : ℝ → Fin K → ℝ) (hτ : DelayFunction τ)
    (Ψ : Path K → Path K → Path K) (hΨ : IsEstimator τ Ψ)
    (Q A : Ω → Path K) (hnet : IsJSEQNetwork u v lam mu τ Ψ Q A)
    (ω : Ω) (hω : GoodPath u v ω) (k : Fin K) :
    (∀ t, 0 ≤ t →
      Qhat n Q ω t k = Gamma1 (fun s => Ahat n mu A ω s k - Shat n v mu ω (busyTime (Q ω) k s) k) t ∧
      Lhat n mu Q ω t k =
        skorokhodReg (fun s => Ahat n mu A ω s k - Shat n v mu ω (busyTime (Q ω) k s) k) t) ∧
    MonotoneOn (fun t => Lhat n mu Q ω t k) (Set.Ici 0) ∧
    StieltjesComplementary (fun t => Qhat n Q ω t k) (fun t => Lhat n mu Q ω t k) := by sorry

end JSEQDelay.Diffusion
