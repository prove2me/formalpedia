-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_workspace_address_costs
-- name    : HardCoreLocalSampling.Local.workspace_address_costs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:00.990352+00:00
-- url     : https://prove2.me/theorems/d00cc9f3-4c95-42d3-89b6-41715d7d5eda
-- title:
--   Lemma 18 — Workspace and address costs
-- statement:
--   Let $W$ be the total intrinsic work of one local-sampler invocation, counting oracle queries and label/address operations at unit cost and all remaining arithmetic at bit cost. Uniformly over inputs, $\mathbb EW^2=O_{\Delta,\lambda}(1)$. The sampler admits an implementation whose expected non-oracle bit cost, including label and address lengths, is $O_{\Delta,\lambda}(\operatorname{polylog}(n+2))$.
--
--   Both bounds are for one and the same exact program, so the second is really a statement about address lengths during the first's run.
--
--   Differences from the source:
--   - encoding: an algorithm in the informally described word and bit cost model → a finite program of the Machine language; reason: a concrete instruction set of that model; every such program is an algorithm in the source's model, and restricting address arithmetic to increment, decrement and paid conversion only charges more than the source does
--   - encoding: the local sampler of the preceding sections → a program exact on all valid inputs, whose existence is asserted together with the two bounds; reason: the lemma is about the sampler constructed earlier; asserting exactness pins it down without restating that construction
--   - encoding: labels of O(log(n+2)) bits → for each κ, labels of at most κ⌈log₂(n+2)⌉ bits, with the second-moment bound chosen before κ; reason: κ is the implied constant; word costs do not see label lengths
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 18, printed p.14 (PDF p.15)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Params
import Definitions.Def_HardCoreLocalSampling_Local_Instance

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Lemma 18, printed p.14 (PDF p.15).
The local sampler has an implementation whose total intrinsic work `W` satisfies
`E W² = O_{Δ,λ}(1)` uniformly over inputs, and whose expected non-oracle bit cost, including label
and address lengths, is `O_{Δ,λ}(polylog(n+2))`. -/
theorem workspace_address_costs (Delta : ℕ) (lam : ℚ) (hS : Standing Delta lam) :
    ∃ (P : Program) (Cw : NNReal), ∀ κ : ℕ, ∃ (Cb : NNReal) (e : ℕ),
      ∀ (I : LocalInstance), ValidInput I Delta → I.LabelsBounded κ → ∀ v : I.vertices,
        ExactUnoccupiedBit P I lam v ∧
        ∫⁻ ω, (wordWork P I.oracle ω noExt (queryConfig v)) ^ 2 ∂fairMeasure ≤ Cw ∧
        ∫⁻ ω, bitWork P I.oracle ω noExt (queryConfig v) ∂fairMeasure ≤
          polylogBound Cb e I.n := by sorry

end HardCoreLocalSampling.Local
