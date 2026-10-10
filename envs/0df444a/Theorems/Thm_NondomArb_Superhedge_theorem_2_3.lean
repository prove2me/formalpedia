-- Prove2me | Theorems.Thm_NondomArb_Superhedge_theorem_2_3
-- name    : NondomArb.Superhedge.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:23:10.591138+00:00
-- url     : https://prove2.me/theorems/88c35a59-9555-43e4-8bd4-f518f2181a90
-- title:
--   Theorem 2.3 — under NA(𝒫), π(f) > −∞ and an optimal superhedging strategy exists
-- statement:
--   Work in the general setting of §2 (measurable space with filtration, a nonempty family $\mathcal P$ of probability measures, measurable $\mathbb R^d$-valued $S_0,\dots,S_T$, predictable strategies $H$).
--
--   **Theorem.** Let NA($\mathcal P$) hold and let $f$ be a random variable. Then
--   $$\pi(f):=\inf\{x\in\mathbb R:\ \exists H,\ x+H\bullet S_T\ge f\ \ \mathcal P\text{-q.s.}\}>-\infty,$$
--   and there exists a predictable $H$ such that $\pi(f)+H\bullet S_T\ge f$ $\mathcal P$-q.s.
--
--   The theorem gives existence of an optimal superhedging strategy without any duality; it is used to obtain the optimal strategy in the one-period and multi-period superhedging theorems.
--
--   **Formalization Note** $\pi(f)$ is an infimum in `EReal` ($\inf\emptyset=+\infty$); the inequality is in `EReal`, so it is trivially true when $\pi(f)=+\infty$, as on the page.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 10, Theorem 2.3

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_General
open MeasureTheory Filter Topology NondomArb.Superhedge.General

namespace NondomArb.Superhedge

/-- **Theorem 2.3** (p. 10). Under NA(𝒫), for a random variable `f`, the superhedging price
`π(f) > −∞`, and an optimal superhedging strategy exists. -/
theorem theorem_2_3 {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℕ m)
    (Pset : Set (Measure Ω)) (hPne : Pset.Nonempty) (hPprob : ∀ P ∈ Pset, IsProbabilityMeasure P)
    {T d : ℕ} (S : ℕ → Ω → (Fin d → ℝ)) (hS : ∀ t ≤ T, Measurable (S t))
    (hNA : NA Pset ℱ T S) (f : Ω → ℝ) (hf : Measurable f) :
    ⊥ < price Pset ℱ T S f ∧
      ∃ H : ℕ → Ω → (Fin d → ℝ), IsPredictable ℱ T H ∧
        QS Pset (fun ω => (f ω : EReal) ≤ price Pset ℱ T S f + ((wealth T S H ω : ℝ) : EReal)) := by sorry

end NondomArb.Superhedge
