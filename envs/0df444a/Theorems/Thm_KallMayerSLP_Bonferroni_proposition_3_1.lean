-- Prove2me | Theorems.Thm_KallMayerSLP_Bonferroni_proposition_3_1
-- name    : KallMayerSLP.Bonferroni.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:13:59.56543+00:00
-- url     : https://prove2.me/theorems/3b149533-3f73-453d-85a4-b37d29f613dd
-- title:
--   Proposition 3.1: $S_k$ is the $k$-th binomial moment of $\nu$
-- statement:
--   For events $B_1,\dots,B_r$, $r\ge1$, on a probability space, and $k=0,\dots,r$,
--   $$
--   \mathbb E\left[\binom{\nu}{k}\right]=S_k.
--   $$
--   This identity explains the term binomial moment.
--
--   Differences from the source:
--   - encoding: events $B_1,\dots,B_r$ (or variables $v_1,\dots,v_r$) indexed by $1,\dots,r$ → indexed by `Fin r`, that is by $0,\dots,r-1$; reason: Lean convention; same instances
--   - encoding: the number $r$ of events $B_1,\dots,B_r$ (the dimension of $\xi$ with values in $\mathbb R^r$) is left implicit → hypothesis `1 ≤ r`; reason: the family $B_1,\dots,B_r$ starts at $B_1$, so the book has $r\ge1$; the hypothesis excludes only the empty family
--   - encoding: $\binom{\nu}{k}=\nu!/(k!(\nu-k)!)$ → `Nat.choose`, which is $0$ for $k>\nu$; reason: the factorial formula is undefined for $k>\nu$, and the book's proof uses the value $0$ there
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, Proposition 3.1, p.286 (PDF 295)

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_occurrenceCount

open MeasureTheory

namespace KallMayerSLP.Bonferroni

/-- Proposition 3.1: `𝔼[(ν choose k)] = S_k` for `k = 0, …, r`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, Proposition 3.1, p.286 (PDF 295). -/
theorem proposition_3_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (B : Fin r → Set Ω) (hB : ∀ i, MeasurableSet (B i)) (k : ℕ) (hk : k ≤ r) :
    ∫ ω, ((occurrenceCount B ω).choose k : ℝ) ∂μ = binomialMoment μ B k := by sorry

end KallMayerSLP.Bonferroni
