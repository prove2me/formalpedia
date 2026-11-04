-- Prove2me | Theorems.Thm_OAI_SignedSweeps_sector_positive_restriction
-- name    : OAI.SignedSweeps.sector_positive_restriction
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T00:09:53.120466+00:00
-- url     : https://prove2.me/theorems/3ae14558-eec2-4c8c-a814-1aa3c01b7cdf
-- title:
--   Trace of a positive coefficient restricted to a subgroup, in a representation with large constituents
-- statement:
--   This is a quantitative form of the restriction of positive group-algebra elements to a subgroup, for a finite-dimensional representation whose constituents have large dimension.
--
--   Let $i:S_p\to S_n$ be an injective homomorphism, let $f:S_n\to\mathbb{C}$ act as a positive operator in the regular representation, and let $\rho$ be a representation of $S_p$ on a finite-dimensional Hilbert space $E$. For $D>0$, $T\ge0$, suppose that every $\mu\vdash p$ with a nonzero intertwiner $S^\mu\to E$ satisfies $\dim S^\mu\ge D$, and moreover every $\lambda\vdash n$ with a nonzero $S_p$-intertwiner $S^\mu\to S^\lambda$ satisfies
--
--   $$
--   \dim S^\lambda\,\operatorname{Re}\operatorname{Tr}_{S^\lambda}\pi_\lambda(f)\le T.
--   $$
--
--   Then, with $\pi(f)=\sum_gf(g)\pi(g)$ and $p(n)$ the number of partitions of $n$,
--
--   $$
--   \operatorname{Re}\operatorname{Tr}_E\,\rho(f\circ i)\le\frac{\dim E}{D^2}\cdot\frac{p!}{n!}\cdot p(n)\cdot T.
--   $$
--
--   It carries the exact index of the subgroup into the local stabilizer traces of the signed sweep induction.
--
--   **Formalization Note** The upstream statement is reproduced verbatim from `ProjectionTrace.lean`.
-- source:
--   OpenAI, "Signed tensor densities and diagram budgets for the Thorp shuffle" (September 26, 2026), openai/math preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf, Section 3, Lemma 3.3, eq. (13), and Lemma 3.5. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SignedSweeps/ProjectionTrace.lean#L81-L164

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs
import Definitions.Def_OAISignedSweepsProofDefs2

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

theorem sector_positive_restriction {p n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup p) E)
    (i : SymmetricGroup p →* SymmetricGroup n) (hi : Function.Injective i)
    (f : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (D T : ℝ) (hD : 0 < D) (hT : 0 ≤ T)
    (hdegree : ∀ mu : Partition p,
      (∃ k : Representation.IntertwiningMap (spechtRepresentation mu) ρ, k ≠ 0) →
        D ≤ spechtDimension mu)
    (hambient : ∀ mu : Partition p,
      (∃ k : Representation.IntertwiningMap (spechtRepresentation mu) ρ, k ≠ 0) →
      ∀ lam : Partition n,
        (∃ k : Representation.IntertwiningMap (spechtRepresentation mu)
          ((spechtRepresentation lam).comp i), k ≠ 0) →
        (spechtDimension lam : ℝ) *
          (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re ≤ T) :
    (LinearMap.trace ℂ E (coefficientAction ρ (fun g => f (i g)))).re ≤
      (finrank ℂ E : ℝ) *
        (((p.factorial : ℝ) / n.factorial) * (Fintype.card (Partition n) : ℝ) * T) / D^2 := by sorry

end SignedSweeps
end
end OAI
