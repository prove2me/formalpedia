-- Prove2me | Theorems.Thm_NondomArb_Superhedge_theorem_3_1
-- name    : NondomArb.Superhedge.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:52.353321+00:00
-- url     : https://prove2.me/theorems/c61bf8a5-1bd5-46fb-b377-2adffd0b2f42
-- title:
--   Theorem 3.1 — one-period FTAP: NA(𝒫) iff every P ∈ 𝒫 is dominated by some Q ∈ 𝒬
-- statement:
--   Consider the one-period market of §3: a nonempty convex set $\mathcal P$ of probability measures and a measurable increment $\Delta S:\Omega\to\mathbb R^d$, with $\mathcal Q=\{Q\in\mathfrak P(\Omega): Q\lll\mathcal P,\ E_Q[\Delta S]=0\}$.
--
--   **Theorem.** The following are equivalent:
--   1. NA($\mathcal P$) holds;
--   2. for all $P\in\mathcal P$ there exists $Q\in\mathcal Q$ such that $P\ll Q$.
--
--   This is the one-period first fundamental theorem of asset pricing under model uncertainty, a building block of the multi-period theorem.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 13, Theorem 3.1

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_OnePeriod
open MeasureTheory Filter Topology NondomArb.Superhedge.OnePeriod

namespace NondomArb.Superhedge

/-- **Theorem 3.1** (p. 13). In the one-period market, NA(𝒫) holds if and only if every `P ∈ 𝒫`
is absolutely continuous with respect to some `Q ∈ 𝒬`. -/
theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω))
    (hP : IsConvexModelSet Pset) {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) (hΔS : Measurable ΔS) :
    NA Pset ΔS ↔ ∀ P ∈ Pset, ∃ Q ∈ MartMeasures Pset ΔS, P ≪ Q := by sorry

end NondomArb.Superhedge
