-- Prove2me | Theorems.Thm_OnlineCAP_Supplement_theorem_5_4
-- name    : OnlineCAP.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:23:46.815547+00:00
-- url     : https://prove2.me/theorems/121fa008-1284-4158-b3ee-de41ec5c6939
-- title:
--   Theorem 5.4 — no fractional $o(\log n)$-competitive algorithm for OCycAP with cut arrivals
-- statement:
--   There is a constant $c>0$ such that for every sufficiently large $n$ there is a set $L$ of links (pairs of distinct vertices) on the cycle $v_0v_1\cdots v_{n-1}v_0$, each of cost $1$, with the following property. For every online fractional algorithm $x$ (nonnegative, nondecreasing over time) there is a valid sequence $s=(C_1,\dots,C_t)$ of 2-cuts such that, if $x$ covers every revealed cut ($\sum_{\ell\text{ crosses }C_i}x_\ell\ge1$ for all $i$), then
--
--   $$\sum_{\ell\in L}x_\ell> c\,\log n\cdot\mathrm{OPT}(s),$$
--
--   where $\mathrm{OPT}(s)$ is the least number of links crossing all cuts of $s$. In particular no fractional algorithm is $\alpha(n)$-competitive for any $\alpha(n)=o(\log n)$.
--
--   The bound shows that the logarithmic ratio of Theorem 3.3 is optimal even for fractional algorithms, in contrast with the constant ratio of Theorem 5.1 for node arrivals.
--
--   **Formalization Note** $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - reading: "no fractional algorithm … achieves a competitive ratio better than log n" → an explicit c > 0 such that for all large n every fractional algorithm has cost > c · log n · OPT on some valid sequence (Ω(log n)); reason: the proof concludes "the cost of the fractional solution is Ω(log n)" (p.24, about (log₂ n)/2), §5.2 is titled "An Ω(log n) lower bound" and Theorem 1.5 says "no o(log n)-competitive algorithm … even fractionally"; the order-of-magnitude reading for every large n, which implies the o(log n) form
--   - generalization: compared with the optimal offline fractional solution (fractional competitive ratio, §2.2) → compared with the integral offline optimum OPT; reason: OPT_frac ≤ OPT on valid sequences, so cost > c log n · OPT implies cost > c log n · OPT_frac; the proof compares with OPT = 1
--   - encoding: cycle with n nodes, L = (V choose 2), a fractional algorithm that maintains a valid fractional solution → ∃ L without diagonal pairs on the standard cycle; ∀ X : FracOnlineAlg; the conclusion holds for X unless X fails to cover a revealed cut; reason: an infeasible algorithm is not competitive by definition; the paper's L is one witness; same instances
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 5.4, p.23 (PDF p.23); proof pp.23–24; Theorem 1.5, p.3

import Mathlib
import Definitions.Def_OnlineCAP_OnlineHSInstance
import Definitions.Def_OnlineCAP_OnlineHSInstance_OPT
import Definitions.Def_OnlineCAP_OnlineHSInstance_OPTfrac
import Definitions.Def_OnlineCAP_FracOnlineAlg
import Definitions.Def_OnlineCAP_crosses
import Definitions.Def_OnlineCAP_edgeCut
import Definitions.Def_OnlineCAP_IsKCut
import Definitions.Def_OnlineCAP_capInstance
import Definitions.Def_OnlineCAP_cycleEnds
import Definitions.Def_OnlineCAP_cycleInstance

open Filter

namespace OnlineCAP.Supplement

/-- **Theorem 5.4 (no fractional o(log n)-competitive algorithm for OCycAP with cut arrivals).**
Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online
Connectivity Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Theorem 5.4, p.23 (PDF p.23): "There is no fractional algorithm for OCycAP with cut arrivals
that achieves a competitive ratio better than log n." Proved on pp.23–24 as "An Ω(log n) lower
bound" (§5.2); Theorem 1.5, p.3: "there is no o(log n)-competitive algorithm for unweighted OCycAP
under cut-arrivals, even fractionally".

There is a constant `c > 0` such that for every sufficiently large `n` there is a set `L` of
links (pairs of distinct vertices) on the cycle `v₀ ⋯ v_{n−1} v₀` with unit costs such that every
online fractional algorithm `x` faces a valid sequence `s` of 2-cuts on which either some
revealed cut has fractional mass below `1` (the algorithm is infeasible), or its cost
`∑_{ℓ ∈ L} x_ℓ` exceeds `c · log n · OPT(s)`, with `OPT(s)` the integral offline optimum.

**Formalization Note.** Comparing with the integral `OPT` (rather than the fractional optimum of
§2.2) is stronger, since `OPT_frac ≤ OPT` on valid sequences; it is what the proof establishes
(`OPT = 1`, p.24). The order-of-magnitude reading of "better than log n" (the proof gives about
`(log₂ n)/2`) is the `Ω(log n)` of §5.2 with an explicit `c`, for all large `n`; it implies that
no fractional algorithm is `α(n)`-competitive for any `α(n) = o(log n)`. Natural logarithm. -/
theorem theorem_5_4 : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    ∃ L : Finset (Sym2 (Fin n)), (∀ ℓ ∈ L, ¬ ℓ.IsDiag) ∧
      ∀ X : FracOnlineAlg (Sym2 (Fin n)) (Finset (Fin n)),
        ∃ s : List (Finset (Fin n)), (cycleInstance n L (fun _ => 1)).Valid s ∧
          ((∀ C ∈ s, 1 ≤ (cycleInstance n L (fun _ => 1)).mass (X.x s) C) →
            c * Real.log n * (cycleInstance n L (fun _ => 1)).OPT s <
              ∑ ℓ ∈ (cycleInstance n L (fun _ => 1)).G,
                (cycleInstance n L (fun _ => 1)).c ℓ * X.x s ℓ) := by sorry

end OnlineCAP.Supplement
