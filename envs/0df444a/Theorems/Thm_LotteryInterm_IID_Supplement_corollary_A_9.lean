-- Prove2me | Theorems.Thm_LotteryInterm_IID_Supplement_corollary_A_9
-- name    : LotteryInterm.IID.Supplement.corollary_A_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:12:41.713912+00:00
-- url     : https://prove2.me/theorems/b48afd8b-eff1-419c-8ffb-e5a31bbbc459
-- title:
--   Corollary A.9 — $\mathbb E[\phi(v)1\{v\ge t\}]=t\Pr[v\ge t]$ above the lowest type
-- statement:
--   Let $D$ be a value law with lowest type $L$ (density on its support, optional terminal atom at a finite upper end $H$, virtual value $\phi$ with $\phi(H)=H$). Assume either that the support $[L,H]$ is bounded, or that $D$ is regular and satisfies Assumption 3.1, $v\Pr[V>v]\to0$. For every $t\ge L$ the virtual value is integrable on $\{v\ge t\}$ and
--   $$\mathbb E[\phi(v)\,1\{v\ge t\}]=t\Pr[v\ge t],\qquad \mathbb E[\phi(v)\,1\{v>t\}]=t\Pr[v>t].$$
--
--   These identities express posted-price revenue as expected virtual surplus; Theorem 6.5 uses the strict one, also for unbounded α-strongly regular laws. No regularity is assumed in the bounded case.
--
--   Differences from the source:
--   - generalization: E[phi(v) 1{v >= t}] and E[phi(v) 1{v > t}] (the expectations are presupposed to exist) → integrability of phi on {v >= t} is part of the conclusion; reason: a stronger conclusion; it also prevents a Bochner integral of a non-integrable function from defaulting to 0
--   - generalization: a value distribution F supported on [L, H] → the published ValueDist (L = lo) with finite hi, or with any hi provided D is regular and satisfies Assumption 3.1 (VanishingTail); reason: the first disjunct is the printed bounded case; the second covers the unbounded alpha-strongly regular laws to which the proof of Theorem 6.5 applies the corollary, under the standing assumptions of §3.2 and Appendix A (regularity, Assumption 3.1), without which the identity fails (equal-revenue law)
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Corollary A.9, p.40 (PDF p.41); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_ValueDist

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- Corollary A.9: for a law on a bounded support `[lo, hi]` (or, under the paper's
standing assumptions, a regular law with `t Pr[v > t] → 0` on an unbounded support)
and `t ≥ lo`,
`E[ϕ(v) 1{v ≥ t}] = t Pr[v ≥ t]` and `E[ϕ(v) 1{v > t}] = t Pr[v > t]`; the virtual
value is integrable on `{v ≥ t}`, so both expectations exist. -/
theorem corollary_A_9 (D : ValueDist) (hsupp : D.hi ≠ ⊤ ∨ (Regular D ∧ VanishingTail D)) (t : ℝ) (ht : D.lo ≤ t) :
    IntegrableOn (virtualValue D) (Set.Ici t) D.law ∧
    ∫ v in Set.Ici t, virtualValue D v ∂D.law = t * (D.law (Set.Ici t)).toReal ∧
    ∫ v in Set.Ioi t, virtualValue D v ∂D.law = t * (D.law (Set.Ioi t)).toReal := by sorry

end LotteryInterm.IID.Supplement
