-- Prove2me | Theorems.Thm_FoundationsRL_TailBounds_lemma_37
-- name    : FoundationsRL.TailBounds.lemma_37
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:23:40.996217+00:00
-- url     : https://prove2.me/theorems/71c55522-176d-4505-aec0-4ea38bd5849e
-- title:
--   Lemma 37 — expected conditional squared Hellinger distance is at most four times the joint one
-- statement:
--   Let $P$ and $Q$ be distributions of a pair $(X,Y)$, with $X$-marginals $P_X,Q_X$ and conditional laws $P_{Y\mid X},Q_{Y\mid X}$, so that $P_{X,Y}=P_X\otimes P_{Y\mid X}$ and $Q_{X,Y}=Q_X\otimes Q_{Y\mid X}$. Then
--   $$
--   \mathbb E_{X\sim P_X}\Big[D^2_{\mathrm H}\big(P_{Y\mid X},Q_{Y\mid X}\big)\Big]\le4\,D^2_{\mathrm H}\big(P_{X,Y},Q_{X,Y}\big),
--   $$
--   where $D^2_{\mathrm H}(P,Q)=\int(\sqrt{dP}-\sqrt{dQ})^2$ is the squared Hellinger distance (no factor $\tfrac12$).
--
--   The joint discrepancy thus controls the discrepancy of the conditional laws on average under $P_X$, even though the two marginals may differ. It is used to pass from Hellinger estimation guarantees on observation pairs to guarantees on the conditional model.
--
--   **Formalization Note** The conditional laws are Markov kernels given as data, and the joint laws are the compositions $P_X\otimes_m\kappa$, $Q_X\otimes_m\eta$; any versions of the kernels may be used. The space assumption (the $X$-space countable or the $Y$-space countably generated, e.g. standard Borel) makes the densities of the kernels jointly measurable. $D^2_{\mathrm H}$ is the series' published definition, valued in $[0,\infty]$, and the expectation is a Lebesgue integral.
--
--   Differences from the source:
--   - reading: any distributions P and Q over a pair (X, Y), with their conditional laws P_{Y|X}, Q_{Y|X} → X-marginals and Markov kernels as data, joint laws PX ⊗ₘ κ and QX ⊗ₘ η, on spaces with the X-space countable or the Y-space countably generated; reason: the source does not say on which spaces P_{Y|X} is defined; a conditional law is a regular conditional distribution, which exists for every joint law when Y is standard Borel (covered), and the class makes the conditional densities measurable, without which the left side need not be an integral of a measurable function
--   - encoding: real-valued D²_H and expectation → values in [0, ∞] (lintegral); reason: Lean convention; for probability measures D²_H ≤ 2, same instances
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 37, p. 158

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_hellingerSq
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FoundationsRL.TailBounds

/-- **Lemma 37.** For any distributions `P` and `Q` over a pair of random variables `(X, Y)`,
`E_{X∼P_X}[D²_H(P_{Y|X}, Q_{Y|X})] ≤ 4 D²_H(P_{X,Y}, Q_{X,Y})`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Lemma 37, p. 158.

**Formalization Note.** A joint law is given by its `X`-marginal and its conditional law of `Y`
given `X`, a Markov kernel: `P_{X,Y} = P_X ⊗ P_{Y|X}` (`PX ⊗ₘ κ`) and `Q_{X,Y} = Q_X ⊗ Q_{Y|X}`
(`QX ⊗ₘ η`). The class `CountableOrCountablyGenerated 𝒳 𝒴` (`𝒳` countable or `𝒴` countably
generated, e.g. standard Borel) makes the conditional densities jointly measurable. `D²_H` is the
series' published `FoundationsRL.DECLower.hellingerSq` (no factor `1/2`, values in `[0, ∞]`); the
expectation over `X ∼ P_X` is a lower Lebesgue integral. Any versions of the kernels may be used. -/
theorem lemma_37 {𝒳 𝒴 : Type*} [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    [MeasurableSpace.CountableOrCountablyGenerated 𝒳 𝒴]
    (PX QX : Measure 𝒳) [IsProbabilityMeasure PX] [IsProbabilityMeasure QX]
    (κ η : Kernel 𝒳 𝒴) [IsMarkovKernel κ] [IsMarkovKernel η] :
    ∫⁻ x, FoundationsRL.DECLower.hellingerSq (κ x) (η x) ∂PX ≤
      4 * FoundationsRL.DECLower.hellingerSq (PX ⊗ₘ κ) (QX ⊗ₘ η) := by sorry

end FoundationsRL.TailBounds
