-- Prove2me | Theorems.Thm_FriedgutCoalition_fact_2_4
-- name    : FriedgutCoalition.fact_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:25.692587+00:00
-- url     : https://prove2.me/theorems/7afb915b-04c3-4676-926b-1477a0933551
-- title:
--   Fact 2.4 — data processing inequality for statistical distance
-- statement:
--   Let $\Omega,\Omega'$ be finite sets and let $\mathbf X,\mathbf Y$ be distributions on $\Omega$ with $|\mathbf X-\mathbf Y|\le\varepsilon$. Then for every $f:\Omega\to\Omega'$,
--
--   $$|f(\mathbf X)-f(\mathbf Y)|\le\varepsilon,$$
--
--   where $|\cdot|$ is the statistical distance and $f(\mathbf X)$ is the law of $f$ applied to a sample of $\mathbf X$.
--
--   Claim 2.5 is its special case $\Omega'=\{0,1\}$.
--
--   Differences from the source:
--   - encoding: distributions X, Y; the law f(X) → weight functions with IsDistribution; pushLaw f X; reason: Lean convention; the same objects
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Fact 2.4, p.7 (statistical distance, §2.3, p.7)

import Mathlib
import Definitions.Def_FriedgutCoalition_prodLaw
import Definitions.Def_IsingLTL_BeliefProp_TVDist

namespace FriedgutCoalition

/-- **Fact 2.4** (data processing inequality; Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…), p.7). Let `Ω, Ω'` be
finite sets and `X, Y` distributions on `Ω` with `|X − Y| ≤ ε`. Then for every `f : Ω → Ω'`,
`|f(X) − f(Y)| ≤ ε`.

**Formalization Note.** Distributions are weight functions (`IsingLTL.BeliefProp.IsDistribution`),
`|· − ·|` is `IsingLTL.BeliefProp.tvDist` (`½ ℓ¹`), and `f(X)` is `pushLaw f X`. `ε` is any real,
as printed. -/
theorem fact_2_4 {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (X Y : Ω → ℝ)
    (hX : IsingLTL.BeliefProp.IsDistribution X) (hY : IsingLTL.BeliefProp.IsDistribution Y)
    (ε : ℝ) (hXY : IsingLTL.BeliefProp.tvDist X Y ≤ ε) (f : Ω → Ω') :
    IsingLTL.BeliefProp.tvDist (pushLaw f X) (pushLaw f Y) ≤ ε := by sorry

end FriedgutCoalition
