-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_theorem_4_2
-- name    : MinCostArbPacking.Main.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:36.821206+00:00
-- url     : https://prove2.me/theorems/57da43f6-bea8-43b4-9601-072db5ad3b9d
-- title:
--   Theorem 4.2 — relaxation theorem
-- statement:
--   **Theorem 4.2 (Relaxation theorem).** Let $M$ be a matroid on a finite set partitioned into classes $E_v$, $c$ real costs, and $I$ extreme with class counts $b$ (independent with $c(I)=\mathrm{OPT}(b)$).
--
--   1. If $\mathrm{OPT}(b+\mathbf 1_u)<+\infty$, an augmenting path from class $u$ exists. For every shortest augmenting path $P$ from class $u$, $I\oplus P$ is independent with class counts $b+\mathbf 1_u$ and $\ell(P)=\Delta_u$.
--   2. For every $U\subseteq V$,
--   $$\mathrm{OPT}(b+\mathbf 1_U)\ \ge\ \mathrm{OPT}(b)+\sum_{u\in U}\Delta_u .$$
--
--   Part 1 relaxes one class optimally; part 2 shows that executing several element-disjoint shortest paths together keeps optimality.
--
--   **Formalization Note** $\mathrm{OPT}$ and $\Delta_u$ are extended reals, $+\infty$ when infeasible; augmenting paths live in $D_{M,N_b}(I)$ for the current $b$ (Remark 4.1).
--
--   Differences from the source:
--   - reading: (a) second sentence, after "If OPT(b+1_u) < +∞" → stated for every shortest augmenting path from class $u$, without the finiteness hypothesis; reason: a shortest path exists only when some path exists, and the proof (pp.21–22) uses the finiteness only to make $\hat\Delta_u$ finite, which a path already does
--   - encoding: $\mathrm{OPT}(b)\in\mathbb R\cup\{+\infty\}$ → `EReal`; reason: $\mathrm{OPT}(b)=c(I)$ is finite, so no $\top-\top$ occurs
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.1, p.10, Theorem 4.2 (proof §4.5, pp.20–22)

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Exchange
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Theorem 4.2 (Relaxation theorem), p.10: a matroid `M` on `α`, classes `E_v = cls⁻¹(v)`, costs
`c`, and `I` extreme with class counts `b`.
(a) If `OPT(b + 1_u) < +∞`, an augmenting path from class `u` exists; for every shortest augmenting
path `P` from class `u`, `I ⊕ P` is independent with class counts `b + 1_u` and `ℓ(P) = ∆_u`.
(b) For every `U ⊆ V`, `OPT(b + 1_U) ≥ OPT(b) + Σ_{u∈U} ∆_u`. -/
theorem theorem_4_2 {α V : Type} [Fintype α] [DecidableEq α] [Fintype V] [DecidableEq V] (M : Matroid α) (hM : M.E = Set.univ) (cls : α → V) (c : α → ℝ)
    (I : Finset α) (hI : ExtremeP (matInd M) cls c I) :
    (∀ u, OPT (matInd M) cls c (addOne (classCount cls I) {u}) < ⊤ →
      ∃ P, IsAugPathFrom (matInd M) cls I u P) ∧
    (∀ u P, IsShortestAmong (IsAugPathFrom (matInd M) cls I u) c I P →
      matInd M (symmDiff I P.toFinset) ∧
        classCount cls (symmDiff I P.toFinset) = addOne (classCount cls I) {u} ∧
        (pathCost c I P : EReal) = Delta (matInd M) cls c (classCount cls I) u) ∧
    (∀ U : Finset V, OPT (matInd M) cls c (classCount cls I) +
        ∑ u ∈ U, Delta (matInd M) cls c (classCount cls I) u ≤
      OPT (matInd M) cls c (addOne (classCount cls I) U)) := by sorry

end MinCostArbPacking.Main
