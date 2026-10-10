-- Prove2me | Theorems.Thm_NondomArb_Superhedge_lemma_3_3
-- name    : NondomArb.Superhedge.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:38.541537+00:00
-- url     : https://prove2.me/theorems/c347827c-7ec3-459e-b2a2-5e6d18092239
-- title:
--   Lemma 3.3 (Fundamental lemma) — under NA(𝒫), 0 ∈ ri{E_R[ΔS] : R ⋘ 𝒫, E_R[|ΔS| + |f|] < ∞}
-- statement:
--   Consider the one-period market of §3: a nonempty convex set $\mathcal P$ of probability measures on $(\Omega,\mathcal F)$ and a measurable increment $\Delta S:\Omega\to\mathbb R^d$.
--
--   **Lemma (Fundamental lemma).** Let NA($\mathcal P$) hold and let $f$ be a random variable. Then
--   $$0\in\operatorname{ri}\{E_R[\Delta S]:\ R\in\mathfrak P(\Omega),\ R\lll\mathcal P,\ E_R[|\Delta S|+|f|]<\infty\}\subseteq\mathbb R^d .$$
--   Similarly, for every $P\in\mathcal P$,
--   $$0\in\operatorname{ri}\{E_R[\Delta S]:\ R\in\mathfrak P(\Omega),\ P\ll R\lll\mathcal P,\ E_R[|\Delta S|+|f|]<\infty\}\subseteq\mathbb R^d .$$
--   Here $\operatorname{ri}$ is the relative interior.
--
--   The lemma strengthens the existence of a martingale measure: the means $E_R[\Delta S]$ fill a relative neighbourhood of the origin, which is the key to perturbing approximate martingale measures into true ones.
--
--   **Formalization Note** $\operatorname{ri}$ is Mathlib's `intrinsicInterior ℝ`; $|\Delta S|$ is the sup norm (same finiteness condition as the Euclidean norm); $E_R[\Delta S]$ is a Bochner integral, which is legitimate because of the finiteness condition.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 13, Lemma 3.3

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_OnePeriod
open MeasureTheory Filter Topology NondomArb.Superhedge.OnePeriod

namespace NondomArb.Superhedge

/-- **Lemma 3.3 (Fundamental lemma)** (p. 13). Under NA(𝒫) in the one-period market, the origin
lies in the relative interior of `{E_R[ΔS] : R ∈ 𝔓(Ω), R ⋘ 𝒫, E_R[|ΔS| + |f|] < ∞}`, and also of
the same set restricted to `P ≪ R`, for every `P ∈ 𝒫`. -/
theorem lemma_3_3 {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω))
    (hP : IsConvexModelSet Pset) {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) (hΔS : Measurable ΔS)
    (hNA : NA Pset ΔS) (f : Ω → ℝ) (hf : Measurable f) :
    (0 : Fin d → ℝ) ∈ intrinsicInterior ℝ {v | ∃ R ∈ Theta Pset ΔS f, v = ∫ ω, ΔS ω ∂ R} ∧
      ∀ P ∈ Pset, (0 : Fin d → ℝ) ∈
        intrinsicInterior ℝ {v | ∃ R ∈ Theta Pset ΔS f, P ≪ R ∧ v = ∫ ω, ΔS ω ∂ R} := by sorry

end NondomArb.Superhedge
