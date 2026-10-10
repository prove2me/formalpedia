-- Prove2me | Theorems.Thm_NondomArb_Superhedge_theorem_3_4
-- name    : NondomArb.Superhedge.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:24:08.249482+00:00
-- url     : https://prove2.me/theorems/a42423bb-d6e3-44b1-9389-5729b08053a1
-- title:
--   Theorem 3.4 — one-period superhedging duality: sup_{Q∈𝒬} E_Q[f] = π(f) > −∞, attained by some H
-- statement:
--   Consider the one-period market of §3 (nonempty convex $\mathcal P$, measurable increment $\Delta S$, $\mathcal Q=\{Q\lll\mathcal P: E_Q[\Delta S]=0\}$), with expectations taken in the extended sense (1.1).
--
--   **Theorem.** Let NA($\mathcal P$) hold and let $f$ be a random variable. Then
--   $$\sup_{Q\in\mathcal Q}E_Q[f]=\pi(f):=\inf\{x\in\mathbb R:\ \exists H\in\mathbb R^d,\ x+H\Delta S\ge f\ \ \mathcal P\text{-q.s.}\}.$$
--   Moreover, $\pi(f)>-\infty$, and there exists $H\in\mathbb R^d$ such that $\pi(f)+H\Delta S\ge f$ $\mathcal P$-q.s.
--
--   This is the one-period superhedging theorem; the multi-period duality is obtained by applying a measurable version of it (Lemma 4.10) recursively.
--
--   **Formalization Note** $E_Q[f]$ is the extended expectation (1.1) in `EReal` ($f$ need not be $Q$-integrable); the supremum and the infimum are taken in `EReal`.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 15, Theorem 3.4, (3.2)

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_OnePeriod
open MeasureTheory Filter Topology NondomArb.Superhedge.OnePeriod

namespace NondomArb.Superhedge

/-- **Theorem 3.4** (p. 15). One-period superhedging duality: under NA(𝒫),
`sup_{Q ∈ 𝒬} E_Q[f] = π(f)`, `π(f) > −∞`, and an optimal `H ∈ ℝ^d` exists. -/
theorem theorem_3_4 {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω))
    (hP : IsConvexModelSet Pset) {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) (hΔS : Measurable ΔS)
    (hNA : NA Pset ΔS) (f : Ω → ℝ) (hf : Measurable f) :
    (⨆ Q ∈ MartMeasures Pset ΔS, extExp Q (fun ω => (f ω : EReal))) = price Pset ΔS f ∧
      ⊥ < price Pset ΔS f ∧
      ∃ H : Fin d → ℝ,
        QS Pset (fun ω => (f ω : EReal) ≤ price Pset ΔS f + ((H ⬝ᵥ ΔS ω : ℝ) : EReal)) := by sorry

end NondomArb.Superhedge
