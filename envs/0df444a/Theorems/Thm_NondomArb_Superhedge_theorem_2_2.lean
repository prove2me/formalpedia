-- Prove2me | Theorems.Thm_NondomArb_Superhedge_theorem_2_2
-- name    : NondomArb.Superhedge.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:31.139479+00:00
-- url     : https://prove2.me/theorems/1d7302ff-d1a1-4b78-84a2-d77cc66d0356
-- title:
--   Theorem 2.2 — under NA(𝒫), the cone 𝒞 = {H • S_T} − L⁰₊ is closed under 𝒫-q.s. convergence
-- statement:
--   Work in the general setting of §2: a measurable space $(\Omega,\mathcal F)$ with filtration $(\mathcal F_t)_{t=0,\dots,T}$, a nonempty family $\mathcal P$ of probability measures, and $\mathcal F$-measurable $\mathbb R^d$-valued $S_0,\dots,S_T$. Let
--   $$\mathcal C:=\{H\bullet S_T:\ H\text{ predictable}\}-\mathcal L^0_+ .$$
--
--   **Theorem.** If NA($\mathcal P$) holds, then $\mathcal C$ is closed under $\mathcal P$-q.s. convergence: if $W^n\in\mathcal C$ for all $n\ge1$ and $W$ is a random variable with $W^n\to W$ $\mathcal P$-q.s., then $W\in\mathcal C$.
--
--   This closedness property is what yields the existence of optimal superhedging strategies (Theorem 2.3), and it is used again to pass to the limit in the superhedging duality.
--
--   **Formalization Note** Membership in $\mathcal C$ means: there are a predictable $H$ and a measurable $K\ge0$ with $W=H\bullet S_T-K$ $\mathcal P$-q.s. (the reading the paper uses in the proof of Theorem 2.3). The $W^n$ are random variables, as elements of $\mathcal C$ are.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 10, Theorem 2.2

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_General
open MeasureTheory Filter Topology NondomArb.Superhedge.General

namespace NondomArb.Superhedge

/-- **Theorem 2.2** (p. 10). Under NA(𝒫), the cone `𝒞 = {H • S_T : H ∈ ℋ} − L⁰₊` is closed under
`𝒫`-q.s. convergence (membership in `𝒞` read up to `𝒫`-polar sets). -/
theorem theorem_2_2 {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m)
    (Pset : Set (Measure Ω)) (hPne : Pset.Nonempty) (hPprob : ∀ P ∈ Pset, IsProbabilityMeasure P)
    {T d : ℕ} (S : ℕ → Ω → (Fin d → ℝ)) (hS : ∀ t ≤ T, Measurable (S t))
    (hNA : NA Pset ℱ T S)
    (W : ℕ → Ω → ℝ) (hWmeas : ∀ n, Measurable (W n)) (hWC : ∀ n, InCone Pset ℱ T S (W n))
    (Wlim : Ω → ℝ) (hWlim : Measurable Wlim)
    (hconv : QS Pset (fun ω => Tendsto (fun n => W n ω) atTop (𝓝 (Wlim ω)))) :
    InCone Pset ℱ T S Wlim := by sorry

end NondomArb.Superhedge
