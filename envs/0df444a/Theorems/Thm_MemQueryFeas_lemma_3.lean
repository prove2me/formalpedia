-- Prove2me | Theorems.Thm_MemQueryFeas_lemma_3
-- name    : MemQueryFeas.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:35:38.720244+00:00
-- url     : https://prove2.me/theorems/bb4fb256-ec79-4e42-8f1b-f65e2798a8d1
-- title:
--   Lemma 3 — iterated stretchings keep regions in the annulus $\frac12\le\|x\|\le\sqrt{p+1}$
-- statement:
--   Let $P\ge2$ and let $R_0\subseteq B$ (the closed unit ball of $\mathbb R^d$) satisfy $\|x\|\ge1/2$ for all $x\in R_0$. For $p\in[P]$ let $U_p,\tilde U_p$ be $k$-dimensional subspaces and $0<\tilde\delta_p<\delta_p<1/2$, and define iteratively
--   $$
--   R_p=T_{U_p,\delta_p^{-1}}\big(R_{p-1}\cap(\tilde U_p^\perp+\tilde\delta_pB)\big). \tag{4.1}
--   $$
--   Suppose $\theta_{\max}(U_p,\tilde U_p)\le\delta_p/\sqrt{3P}$ and $\tilde\delta_p/\delta_p\le1/3$ for all $p\in[P]$. Then for every $p\in[P]$ and every $x\in R_p$,
--   $$
--   \tfrac12\le\|x\|\le\sqrt{p+1}.
--   $$
--
--   Although each stretch $T_{U_p,\delta_p^{-1}}$ enlarges the space by a factor up to $1/\delta_p$, the regions of the construction stay bounded; this is used to bound the phase regions (Corollary 2) and in the validity proof of the hard instance.
--
--   Differences from the source:
--   - encoding: 1/2 ≤ inf_{x∈R_p} ‖x‖ ≤ sup_{x∈R_p} ‖x‖ ≤ √(p+1) → for every x ∈ R_p, 1/2 ≤ ‖x‖ ≤ √(p+1); reason: equivalent for nonempty R_p; for empty R_p the printed inf/sup chain is degenerate and there is nothing to bound
--   - reading: U_p, Ũ_p ∈ Gr(d, k) → k-dimensional subspaces (Gr(k, d)); reason: typo: Gr(k, d) is the set of k-dimensional subspaces (Notations, p.7)
--   - encoding: Ũ_p^⊥ + δ̃_p B → {x | ∃ y, P_{Ũ_p} y = 0 ∧ ‖x − y‖ ≤ δ̃_p}; reason: the same set, with subspaces given by their projections
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Lemma 3, p.14 (PDF p.15), Eq. (4.1)

import Mathlib
import Definitions.Def_MemQueryFeas_IsOrthProj
import Definitions.Def_MemQueryFeas_thetaMax
import Definitions.Def_MemQueryFeas_stretch

namespace MemQueryFeas

/-- **Lemma 3 (iterated stretchings keep regions in an annulus).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Lemma 3, p.14 (PDF p.15):
"Let `P ≥ 2` and let `R_0 ⊆ B ⊂ ℝ^d` satisfy `inf_{x∈R_0} ‖x‖ ≥ 1/2`. Let `U_p, Ũ_p ∈ Gr(d, k)` and
`0 < δ̃_p < δ_p < 1/2` for all `p ∈ [P]`. For `p ∈ [P]`, iteratively define
`R_p := T_{U_p,δ_p^{−1}}(R_{p−1} ∩ (Ũ_p^⊥ + δ̃_pB))`. (4.1) Suppose `∠max(U_p, Ũ_p) ≤ δ_p/√(3P)` and
`δ̃_p/δ_p ≤ 1/3` for all `p ∈ [P]`. Then we have `1/2 ≤ inf_{x∈R_p} ‖x‖ ≤ sup_{x∈R_p} ‖x‖ ≤ √(p + 1)`."

**Formalization Note.** `B` is the closed unit ball; `U_p, Ũ_p` are `k`-dimensional (`Gr(d,k)` read as
`Gr(k,d)`), given by projections; `Ũ_p^⊥ + δ̃_pB = {x | ∃ y, P_{Ũ_p} y = 0 ∧ ‖x − y‖ ≤ δ̃_p}`. The
inf/sup chain is stated pointwise: every `x ∈ R_p` has `1/2 ≤ ‖x‖ ≤ √(p+1)` (vacuous for empty
`R_p`). -/
theorem lemma_3 (d k P : ℕ) (hP : 2 ≤ P) (R : ℕ → Set (Vec d))
    (hR0 : R 0 ⊆ Metric.closedBall (0 : Vec d) 1) (hR0' : ∀ x ∈ R 0, (1 : ℝ) / 2 ≤ ‖x‖)
    (U Ut : ℕ → Op d) (hU : ∀ p, 1 ≤ p → p ≤ P → IsOrthProj k (U p) ∧ IsOrthProj k (Ut p))
    (δ δt : ℕ → ℝ) (hδ : ∀ p, 1 ≤ p → p ≤ P → 0 < δt p ∧ δt p < δ p ∧ δ p < 1 / 2)
    (hR : ∀ p, 1 ≤ p → p ≤ P →
      R p = stretch (U p) (δ p)⁻¹ '' (R (p - 1) ∩ {x | ∃ y, Ut p y = 0 ∧ ‖x - y‖ ≤ δt p}))
    (hang : ∀ p, 1 ≤ p → p ≤ P → thetaMax (U p) (Ut p) ≤ δ p / Real.sqrt (3 * P))
    (hrat : ∀ p, 1 ≤ p → p ≤ P → δt p / δ p ≤ 1 / 3) :
    ∀ p, 1 ≤ p → p ≤ P → ∀ x ∈ R p, (1 : ℝ) / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ Real.sqrt (p + 1) := by sorry

end MemQueryFeas
