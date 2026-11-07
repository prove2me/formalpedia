-- Prove2me | Theorems.Thm_NCPComm_claim_3_11
-- name    : NCPComm.claim_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:30.403147+00:00
-- url     : https://prove2.me/theorems/bd79a9aa-18fb-43e0-8fef-aa106149e8c7
-- title:
--   Claim 3.11 — discretized normal approximation [Fan14]
-- statement:
--   There is an absolute constant $C$ such that, for $X\sim\mathrm{Bin}(n,p)$ with $0<p<1$ and $Z'=\lceil Z\rceil$ with $Z\sim\mathcal N(np,np(1-p))$,
--   $$
--   \delta_{\mathrm{TV}}(X,Z')\le C\min\Big(1,\frac1{\sqrt{np(1-p)}}\Big).
--   $$
--
--   This is a cited result ([Fan14, Theorem 1.3 and Remark 1.4], adapted by the paper to ceiling rounding). It turns the doubleton counts into normal variables.
--
--   **Formalization Note** Both laws are measures on $\mathbb Z$, compared by the published `MarkovChainCLT.tvDist`, $\sup_A|\mu(A)-\nu(A)|$. At $n=0$ the normal is the point mass at $0$ and Lean's $1/\sqrt0=0$; both sides are then $0$.
--
--   Differences from the source:
--   - encoding: δ_TV as ½Σ|P(x) − Q(x)| → sup_A |μ(A) − ν(A)| on ℤ; reason: the two agree for probability measures on a countable set
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Claim 3.11, p.16

import Mathlib
import Definitions.Def_TotalVariationDist

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Claim 3.11 (Discretized normal approximation, [Fan14]), p.16** (Herman, The Communication
Complexity of Verifying Distribution Properties, STOC 2027 submission, manuscript sha256 714c0353…;
cited result). There is an absolute constant `C` such that, for `X ∼ Bin(n, p)` with `0 < p < 1` and
`Z′ = ⌈Z⌉` with `Z ∼ N(np, np(1-p))`, `δ_TV(X, Z′) ≤ C·min(1, 1/√(np(1-p)))`.

**Formalization Note** Both laws are measures on `ℤ`, and `MarkovChainCLT.tvDist` is the published
`sup_A |μ(A) - ν(A)|`. At `n = 0` the normal is the point mass at `0` and `1/√0 = 0` in Lean; then
both sides are `0`, so the convention changes nothing. -/
theorem claim_3_11 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (p : unitInterval), 0 < (p : ℝ) → (p : ℝ) < 1 →
      MarkovChainCLT.tvDist
          ((ProbabilityTheory.binomial n p).map (Nat.cast : ℕ → ℤ))
          ((ProbabilityTheory.gaussianReal ((n : ℝ) * p)
              (Real.toNNReal ((n : ℝ) * p * (1 - p)))).map fun z : ℝ => ⌈z⌉)
        ≤ C * min 1 (1 / Real.sqrt ((n : ℝ) * p * (1 - p))) := by sorry

end NCPComm
