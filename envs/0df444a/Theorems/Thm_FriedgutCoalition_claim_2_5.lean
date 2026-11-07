-- Prove2me | Theorems.Thm_FriedgutCoalition_claim_2_5
-- name    : FriedgutCoalition.claim_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:33:47.829045+00:00
-- url     : https://prove2.me/theorems/3a13aa86-690a-4cf2-9f53-455e25bc7b80
-- title:
--   Claim 2.5 — statistical distance bounds the difference of expectations of a $\{0,1\}$-valued function
-- statement:
--   Let $\mathbf X,\mathbf Y$ be distributions on a finite set $\Omega$ and let $\varepsilon>0$ with $|\mathbf X-\mathbf Y|\le\varepsilon$, where $|\mathbf X-\mathbf Y|=\tfrac12\sum_{x\in\Omega}|\Pr[\mathbf X=x]-\Pr[\mathbf Y=x]|$. Then for every $f:\Omega\to\{0,1\}$,
--
--   $$\Big|\mathop{\mathbb E}_{x\sim\mathbf X}[f(x)]-\mathop{\mathbb E}_{y\sim\mathbf Y}[f(y)]\Big|\le\varepsilon.$$
--
--   The paper applies it to indicators of output events to transfer expectations and coalition probabilities between the encoded law and the uniform one.
--
--   Differences from the source:
--   - encoding: distributions X, Y on Ω; E_{x∼X}[f(x)] → weight functions with IsDistribution (nonnegative, sum 1); ∑_ω X(ω)·[f ω]; reason: Lean convention; the same objects
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Claim 2.5, p.7 (statistical distance, §2.3, p.7)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist

namespace FriedgutCoalition

/-- **Claim 2.5** (Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…), p.7). Let `X, Y` be distributions on a finite
set `Ω` and `ε > 0` with `|X − Y| ≤ ε`. Then for every `f : Ω → {0,1}`,
`|E_{x∼X}[f(x)] − E_{y∼Y}[f(y)]| ≤ ε`.

**Formalization Note.** Distributions are weight functions (`IsingLTL.BeliefProp.IsDistribution`:
nonnegative, summing to `1`); `|X − Y|` is `IsingLTL.BeliefProp.tvDist` (`½ ℓ¹`); `{0,1}` is `Bool`
and `E_X[f] = ∑_ω X(ω) [f ω]`. -/
theorem claim_2_5 {Ω : Type*} [Fintype Ω] (X Y : Ω → ℝ)
    (hX : IsingLTL.BeliefProp.IsDistribution X) (hY : IsingLTL.BeliefProp.IsDistribution Y)
    (ε : ℝ) (hε : 0 < ε) (hXY : IsingLTL.BeliefProp.tvDist X Y ≤ ε) (f : Ω → Bool) :
    |∑ ω, X ω * (if f ω then 1 else 0) - ∑ ω, Y ω * (if f ω then 1 else 0)| ≤ ε := by sorry

end FriedgutCoalition
