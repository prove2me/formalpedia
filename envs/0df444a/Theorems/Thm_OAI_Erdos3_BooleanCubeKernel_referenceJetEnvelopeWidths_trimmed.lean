-- Prove2me | Theorems.Thm_OAI_Erdos3_BooleanCubeKernel_referenceJetEnvelopeWidths_trimmed
-- name    : OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_trimmed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T18:44:03.73421+00:00
-- url     : https://prove2.me/theorems/0dc157c5-e714-4818-bb92-1158f47beb4a
-- title:
--   Reference jet envelope widths at the trimmed root scale equal 5/2 τ N
-- statement:
--   Let $X$ be a type, $q \in \mathbb N$, $\mathrm{stride}, N : X \to \mathbb N$ with $\mathrm{stride}(x) > 0$ for all $x$, $\tau$ a real, and $z \in \mathrm{Option}(\mathrm{Fin}\,q) \times X$. Then
--   $$\texttt{referenceJetEnvelopeWidths}\ \mathrm{stride}\ (\texttt{trimmedSpatialRootScale}\ \tau\ N\ \mathrm{stride})\ z = \tfrac52\,\tau\,N(z_2),$$
--   where `referenceJetEnvelopeWidths stride H z` $= 20\,\mathrm{stride}(z_2)\,H(z_2)$ and `trimmedSpatialRootScale τ N modulus x` $= \tau N(x)/8/\mathrm{modulus}(x)$ are explicit real-valued functions of OpenAI.
--
--   Lean: `OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_trimmed` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedReferenceJetWindow.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B054` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedReferenceJetWindow.lean#L239

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B054

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

theorem referenceJetEnvelopeWidths_trimmed {X : Type*} {q : ℕ}
    (stride N : X → ℕ) (hs : ∀ x, 0 < stride x) (τ : ℝ) (z : Option (Fin q) × X) :
    referenceJetEnvelopeWidths stride (trimmedSpatialRootScale τ N stride) z =
      (5 / 2 : ℝ) * τ * (N z.2 : ℝ) := by
  sorry

end Erdos3.BooleanCubeKernel
end
end OAI
