-- Prove2me | Theorems.Thm_IntractableCoding_Weights_npHard_of_threeDM_reduction
-- name    : IntractableCoding.Weights.npHard_of_threeDM_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:16.740006+00:00
-- url     : https://prove2.me/theorems/b17086ed-0c85-4dde-ba73-9e9747ac82ea
-- title:
--   Section III, p. 385 — a polynomial-time reduction from THREE-DIMENSIONAL MATCHING makes a problem NP-hard
-- statement:
--   Let $P$ be a decision problem on instances of a type $\alpha$, presented through a binary encoding $\mathrm{enc}$. Suppose $g$ maps every THREE-DIMENSIONAL MATCHING instance $I$ to an instance $g(I)$ of $P$, is computed by a polynomial-time multi-stack Turing machine from the encoding of $I$ to $\mathrm{enc}(g(I))$, and satisfies
--   $$I\text{ has a matching}\iff P(g(I))\qquad\text{for every }I.$$
--   Then $P$ is NP-hard with respect to $\mathrm{enc}$.
--
--   This is the step "a polynomial-time algorithm for COSET WEIGHTS implies a polynomial-time algorithm for THREE-DIMENSIONAL MATCHING, which in turn implies a polynomial-time algorithm for every NP-problem", used once for each of the two coding problems. It rests on the NP-hardness of THREE-DIMENSIONAL MATCHING (Karp's problem 17), published as `PricingWithTips.threeDM_np_hard`.
--
--   Differences from the source:
--   - generalization: the reduction to COSET WEIGHTS (and the same argument for SUBSPACE WEIGHTS) → any target problem P with any binary encoding enc; reason: the paper uses the argument twice with the same shape; taking enc = encodeCoset, P = CosetWeightsYes (resp. encodeSubspace, SubspaceWeightsYes) gives exactly the paper's two uses
--   - reading: a polynomial-time algorithm for COSET WEIGHTS implies one for every NP-problem (Turing style) → NP-hardness under polynomial-time TM2-computed many-one reductions; reason: the paper's reduction is a many-one map and its notion of NP-completeness is Karp's [4]; many-one hardness implies the Turing-style sentence
-- source:
--   Berlekamp, McEliece & van Tilborg, On the Inherent Intractability of Certain Coding Problems, IEEE Trans. Inform. Theory IT-24(3), 1978, https://doi.org/10.1109/TIT.1978.1055873, p. 385, Section III, reduction of THREE-DIMENSIONAL MATCHING to COSET WEIGHTS ("That is, a polynomial-time algorithm for COSET WEIGHTS implies …")

import Mathlib
import Definitions.Def_IntractableCoding_Weights_NPComplete

namespace IntractableCoding.Weights

open PricingWithTips

/-- NP-hardness transfers along a polynomial-time many-one reduction from
THREE-DIMENSIONAL MATCHING: if a map `g` from 3DM instances to instances of `P`, computed by a
polynomial-time TM2 machine from `encodeThreeDMInstance I` to `enc (g I)`, satisfies
`ThreeDMYes I ↔ P (g I)` for every `I`, then `P` is NP-hard (with respect to `enc`). -/
theorem npHard_of_threeDM_reduction {α : Type} (enc : α → List Bool) (P : α → Prop)
    (g : ThreeDMInstance → α)
    (hg : Nonempty (Turing.TM2ComputableInPolyTime encodeThreeDMInstance enc g))
    (hred : ∀ I : ThreeDMInstance, ThreeDMYes I ↔ P (g I)) :
    NPHardFor enc P := by sorry

end IntractableCoding.Weights
