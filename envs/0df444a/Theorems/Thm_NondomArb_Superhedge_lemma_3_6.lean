-- Prove2me | Theorems.Thm_NondomArb_Superhedge_lemma_3_6
-- name    : NondomArb.Superhedge.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:54.69167+00:00
-- url     : https://prove2.me/theorems/65e3d36d-034d-4eab-ba26-26a597896b0e
-- title:
--   Lemma 3.6 — every R ⋘ 𝒫 is within c(1 + |E_R f|)|E_R ΔS| of some Q ∈ 𝒬 in E[f], c independent of R
-- statement:
--   Consider the one-period market of §3 (nonempty convex $\mathcal P$, measurable increment $\Delta S$, martingale measures $\mathcal Q$).
--
--   **Lemma.** Let NA($\mathcal P$) hold and let $f$ be a random variable. There is a constant $c>0$ such that for every $R\in\mathfrak P(\Omega)$ with $R\lll\mathcal P$ and $E_R[|\Delta S|+|f|]<\infty$ there exists $Q\in\mathcal Q$ with $E_Q[|f|]<\infty$ and
--   $$|E_Q[f]-E_R[f]|\le c\,(1+|E_R[f]|)\,|E_R[\Delta S]| .$$
--   The constant $c$ does not depend on $R$ or $Q$.
--
--   The lemma quantifies how far an approximate martingale measure is from a true one, in terms of the expectation of $f$.
--
--   **Formalization Note** The constant is quantified before $R$ ($\exists c>0,\ \forall R,\ \exists Q$). $|E_R[\Delta S]|$ is the sup norm; changing the norm on $\mathbb R^d$ only changes $c$.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 16, Lemma 3.6

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_OnePeriod
open MeasureTheory Filter Topology NondomArb.Superhedge.OnePeriod

namespace NondomArb.Superhedge

/-- **Lemma 3.6** (p. 16). Under NA(𝒫), there is a constant `c > 0` such that every `R ⋘ 𝒫` with
`E_R[|ΔS| + |f|] < ∞` can be perturbed into some `Q ∈ 𝒬` with `E_Q[|f|] < ∞` and
`|E_Q[f] − E_R[f]| ≤ c (1 + |E_R[f]|) |E_R[ΔS]|`. The constant is chosen before `R`. -/
theorem lemma_3_6 {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω))
    (hP : IsConvexModelSet Pset) {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) (hΔS : Measurable ΔS)
    (hNA : NA Pset ΔS) (f : Ω → ℝ) (hf : Measurable f) :
    ∃ c : ℝ, 0 < c ∧ ∀ R ∈ Theta Pset ΔS f, ∃ Q ∈ MartMeasures Pset ΔS, Integrable f Q ∧
      |∫ ω, f ω ∂ Q - ∫ ω, f ω ∂ R| ≤ c * (1 + |∫ ω, f ω ∂ R|) * ‖∫ ω, ΔS ω ∂ R‖ := by sorry

end NondomArb.Superhedge
