-- Prove2me | Theorems.Thm_OAI_CurrentMain_finite_set_central_splitting
-- name    : OAI.CurrentMain.finite_set_central_splitting
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T22:14:42.069188+00:00
-- url     : https://prove2.me/theorems/8e884e1e-07f3-423c-8296-e45962067d7a
-- title:
--   Finite-set central splitting by a projection of half trace (OpenAI uniform property Gamma, Theorem 1.3)
-- statement:
--   **Notation** (the published bundle `Def_UniformGamma` and the definitions bundle `OAIQWCMM000` of this split). For a $C^*$-algebra $D$, a `TracialState` is a positive normalized tracial functional, and the trace 2-norm is $\lVert a\rVert_{2,\tau} = \tau(a^*a)^{1/2}$ (`traceTwoNorm`). `IsNuclear A` asks that every algebraic tensor product of $A$ with a $C^*$-algebra carry at most one $C^*$-norm, and `RealRankZero D` that self-adjoint elements be norm limits of self-adjoint elements with finite spectrum. A projection $g$ is full (`IsFull`) when the closed two-sided ideal it generates is all of $D$. For $a, p, x \in D$:
--   - `uniformTwoNorm a` is $\sup_\tau \lVert a\rVert_{2,\tau}$;
--   - `uniformHalvingError p x` is $\sup_\tau \bigl|\tau(px) - \tfrac12 \tau(x)\bigr|$.
--
--   Both suprema run over the tracial states of $D$.
--
--   **The statement.** Let $A$ and $D$ be $C^*$-algebras (with $D$ carrying its star order), and let $\iota : A \to D$ be an injective $*$-homomorphism of complex algebras. Assume:
--   - $A$ is nuclear;
--   - $D$ has real rank zero and at least one tracial state;
--   - for every $\delta > 0$ there is a full projection $g \in D$ with $\sup_\tau \tau(g) < \delta$.
--
--   Then for every finite set $K$ of unitaries of $A$ and every $\varepsilon > 0$ there is a projection $P \in D$ such that for every $x \in K$,
--   $$\sup_\tau \bigl\lVert P\,\iota(x) - \iota(x)\,P\bigr\rVert_{2,\tau} < \varepsilon \qquad\text{and}\qquad \sup_\tau \bigl|\tau(P\,\iota(x)) - \tfrac12\,\tau(\iota(x))\bigr| < \varepsilon .$$
--
--   This is the paper's Theorem 1.3 (finite-set central splitting), with the inclusion $A \subseteq D$ given as the injective map $\iota$.
--
--   Lean: `OAI.CurrentMain.finite_set_central_splitting`, OpenAI's theorem of that name (in `lean/OAI/Analysis/TracialSplitting/FiniteSplitting.lean`).
-- source:
--   OpenAI, Tracial projection methods and uniform property Gamma, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 291; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Tracial-projection-methods-and-uniform-property-Gamma-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TracialSplitting/FiniteSplitting.lean (declaration OAI.CurrentMain.finite_set_central_splitting)

import Mathlib
import Definitions.Def_UniformGamma
import Definitions.Def_OAIQWCMM000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uNuclear

section

noncomputable section

open Pureness

namespace CurrentMain

theorem finite_set_central_splitting
    {A D : Type} [CStarAlgebra A] [CStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D]
    (ι : A →⋆ₐ[ℂ] D) (_hι : Function.Injective ι)
    (hA : IsNuclear.{0, uNuclear} A) (hD : RealRankZero D)
    (hT : Nonempty (TracialState D))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : TracialState D, (τ.functional g).re) < δ)
    (K : Finset (unitary A)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : D, IsStarProjection P ∧ ∀ x ∈ K,
      uniformTwoNorm (P * ι (x : A) - ι (x : A) * P) < ε ∧
      uniformHalvingError P (ι (x : A)) < ε := by
  sorry

end CurrentMain

end

end

end OAI
end
