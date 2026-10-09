-- Prove2me | Theorems.Thm_LocalPF_Block_theorem_4_14
-- name    : LocalPF.Block.theorem_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:16.526983+00:00
-- url     : https://prove2.me/theorems/a6c00090-1d3b-4d53-90bf-9e0b3f1e70fb
-- title:
--   Theorem 4.14, p. 49 — bias term: ‖π^x_n − π̃^x_n‖_J ≤ 8e^{−β}(1−e^{−β})⁻¹(1−ε^{2Δ}) card J e^{−βd(J,∂K)}
-- statement:
--   Consider the local model of the Setting file with neighbourhood size $r\ge1$, a partition $\mathcal K$ of $V$ into nonempty blocks, and a fixed observation sequence. Suppose the observation densities are strictly positive and $\psi^v$-integrable in the state variable, and that there is $\varepsilon>0$ with
--   $$\varepsilon\le p^v(x,z^v)\le\varepsilon^{-1}\qquad\text{for all }v\in V,\ x,z\in\mathbb X,$$
--   and
--   $$\varepsilon>\varepsilon_0=\Big(1-\frac1{18\Delta^2}\Big)^{1/2\Delta}.$$
--   Let $\beta=-(2r)^{-1}\log 18\Delta^2(1-\varepsilon^{2\Delta})>0$. Then
--   $$\|\pi^x_n-\tilde\pi^x_n\|_J\le\frac{8e^{-\beta}}{1-e^{-\beta}}(1-\varepsilon^{2\Delta})\operatorname{card}J\,e^{-\beta d(J,\partial K)}$$
--   for every $n\ge0$, $x\in\mathbb X$, $K\in\mathcal K$ and $J\subseteq K$. Here $\pi^x_n$ is the filter and $\tilde\pi^x_n$ the block filter, both started at $\delta_x$.
--
--   This is the bias half of the main theorem: the error introduced by the blocking step decays exponentially in the distance to the block boundary, uniformly in time and in the dimension $\operatorname{card}V$.
--
--   **Formalization Note** The bound is written in terms of $q=e^{-\beta}=(18\Delta^2(1-\varepsilon^{2\Delta}))^{1/(2r)}$, so that $e^{-\beta d}=q^d$; this also covers $\varepsilon=1$, where $\beta=+\infty$ and the bound is $0$. $e^{-\beta d(J,\partial K)}=0$ when $d(J,\partial K)=+\infty$. The paper assumes no bounds on $g^v$ here; the added hypothesis that $g^v>0$ and $g^v(\cdot,y)$ is $\psi^v$-integrable is what makes the Bayes formula of the filter well defined (positive, finite normaliser), and it is implied by the $\kappa$-bounds of Theorem 2.1. The bound holds for every observation sequence (Remark 2.4).
-- source:
--   Rebeschini & van Handel, Can Local Particle Filters Beat the Curse of Dimensionality?, arXiv:1301.6585v2 (reprint of Ann. Appl. Probab. 25(5), 2015), p. 49, Theorem 4.14

import Mathlib
import Definitions.Def_LocalPF_Block_Setting

open MeasureTheory
open scoped ENNReal

namespace LocalPF.Block

/-- Theorem 4.14 (Bias term), p. 49. Here `q = e^{-β}` with
`β = -(2r)⁻¹ log 18Δ²(1 - ε^{2Δ})`, i.e. `q = (18Δ²(1 - ε^{2Δ}))^{1/(2r)}`. -/
theorem theorem_4_14 {V : Type*} [Fintype V] (G : SimpleGraph V) (r : ℕ) (hr : 1 ≤ r)
    {Xs : V → Type*} [∀ v, TopologicalSpace (Xs v)] [∀ v, PolishSpace (Xs v)]
    [∀ v, MeasurableSpace (Xs v)] [∀ v, BorelSpace (Xs v)]
    {Ys : V → Type*} [∀ v, TopologicalSpace (Ys v)] [∀ v, PolishSpace (Ys v)]
    [∀ v, MeasurableSpace (Ys v)] [∀ v, BorelSpace (Ys v)]
    (ψ : ∀ v, Measure (Xs v)) [∀ v, SigmaFinite (ψ v)]
    (p : ∀ v, (∀ w, Xs w) → Xs v → ℝ) (g : ∀ v, Xs v → Ys v → ℝ)
    (hM : IsLocalModel G r ψ p g)
    {ι : Type*} [Fintype ι] (blk : V → ι) (hblk : Function.Surjective blk)
    (hg_pos : ∀ v ξ η, 0 < g v ξ η)
    (hg_int : ∀ v η, Integrable (fun ξ => g v ξ η) (ψ v))
    (ε : ℝ) (hε : 0 < ε) (hp : ∀ v x z, ε ≤ p v x z ∧ p v x z ≤ ε⁻¹)
    (hε₀ : (1 - 1 / (18 * (maxNbhd G r : ℝ) ^ 2)) ^ ((1 : ℝ) / (2 * (maxNbhd G r : ℝ))) < ε)
    (y : ℕ → ∀ v, Ys v) (x : ∀ v, Xs v) (n : ℕ) (k : ι) (J : Finset V)
    (hJ : J ⊆ block blk k) :
    let Δ := maxNbhd G r
    let q : ℝ := (18 * (Δ : ℝ) ^ 2 * (1 - ε ^ (2 * Δ))) ^ ((1 : ℝ) / (2 * (r : ℝ)))
    locTV (J : Set V) (filt ψ p g y x n) (blockFilt ψ p g blk y x n) ≤
      ENNReal.ofReal (8 * q / (1 - q) * (1 - ε ^ (2 * Δ)) * J.card *
        decayPow q (setDist G J (innerBdry G r (block blk k)))) := by sorry

end LocalPF.Block
