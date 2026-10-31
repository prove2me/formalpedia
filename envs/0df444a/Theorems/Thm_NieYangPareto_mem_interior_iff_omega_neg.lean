-- Prove2me | Theorems.Thm_NieYangPareto_mem_interior_iff_omega_neg
-- name    : NieYangPareto.mem_interior_iff_omega_neg
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:32.717983+00:00
-- url     : https://prove2.me/theorems/e3bed1b6-c4f8-4b98-9797-7126d0481ad5
-- title:
--   Proof of Theorem 3.2 — $v\in\operatorname{int}\operatorname{conv}(\mathcal U)$ iff $\omega^*(v)<0$ or (3.2) is infeasible (corrected: separating, not supporting, hyperplane)
-- statement:
--   Let $m\ge1$, let $K$ have nonempty interior and let $v\in\mathbb R^m$. Then $v$ lies in the interior of $\operatorname{conv}(\mathcal U)$ if and only if the optimal value $\omega^*$ of (3.2) is negative or (3.2) is infeasible; as an extended real,
--
--   $$
--   v\in\operatorname{int}\operatorname{conv}(\mathcal U)\iff\omega^*(v)<0 .
--   $$
--
--   Combined with strong duality this gives the first clause of Theorem 3.2.
--
--   Differences from the source:
--   - encoding: disjoint finite label sets ℰ, ℐ → two finite types E, I (`[Finite E] [Finite I]`), each with its own constraint family; reason: separate types encode disjointness; the same instances
--   - reading: (3.2), (3.3) introduced "for given v ∈ f(K)" (p.8) → v ranges over all of ℝ^m; reason: the proof of Theorem 3.2 (p.9) applies them to arbitrary v
--   - reading: "max" in (3.2) → supremum in EReal, so that ω* = ⊥ exactly when (3.2) is infeasible; reason: the page compares optimal values and speaks of infeasibility; a real supremum would return the junk value 0
--   - reading: m unbounded below ("several objective functions") → hypothesis 0 < m; reason: at m = 0 the equality of (3.3) reads 1 = 0 and eᵀw = 1 reads 0 = 1, so the programs are meaningless there
--   - correction: "A point v lies in the interior of conv(𝒰) if and only if there is no supporting hyperplane for 𝒰 through it", from which the page derives this statement → the conclusion of the page's "Thus" sentence, without that premise; reason: the premise is false: for n = m = 1, ℰ = ℐ = ∅, K = ℝ, f = x² and v = −1, every assumption of Theorem 3.2 holds, no supporting hyperplane passes through v, and v ∉ int conv(𝒰). What the argument needs is a weakly separating hyperplane, which exists at every point outside the interior; the conclusion is true for every v
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, proof of Theorem 3.2, p.9

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_MOP_U
import Definitions.Def_NieYangPareto_Programs

namespace NieYangPareto

/-- **`v ∈ int conv(𝒰)` iff `ω* < 0` or (3.2) is infeasible.** Nie–Yang, arXiv:2108.04336v2, proof
of Theorem 3.2, p.9: "Thus, v lies in the interior of conv(𝒰) if and only if the optimal value ω* of
(3.2) is negative or it is infeasible."

**Formalization Note** Since `sSup ∅ = ⊥`, "negative or infeasible" is exactly `ω*(v) < 0`. The
sentence the page derives this from ("no supporting hyperplane for 𝒰 through it") is false for points
outside `𝒰`: for `n = m = 1`, `K = ℝ`, `f = x²`, `v = -1`, no supporting hyperplane passes through
`v`, and `v ∉ int conv(𝒰)`. The conclusion stated here is true: what the argument needs is a weakly
separating hyperplane. -/
theorem mem_interior_iff_omega_neg {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I)
    (hK : (interior P.K).Nonempty) (hm : 0 < m) (v : Fin m → ℝ) :
    v ∈ interior (convexHull ℝ P.U) ↔ P.omegaStar v < 0 := by sorry

end NieYangPareto
