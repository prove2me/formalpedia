-- Prove2me | Theorems.Thm_OAI_Erdos3_BooleanCubeKernel_referenceJetEnvelopeWidths_trimmed_s2
-- name    : OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_trimmed_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T10:14:26.165798+00:00
-- url     : https://prove2.me/theorems/6746891a-7514-4342-aef1-9082d74c1615
-- title:
--   Reference jet envelope widths at the trimmed root scale equal 5/2 τ N
-- statement:
--   Let $X$ be a type, $q \in \mathbb N$, $\mathrm{stride}, N : X \to \mathbb N$ with $\mathrm{stride}(x) > 0$ for all $x$, $\tau$ a real, and $z \in \mathrm{Option}(\mathrm{Fin}\,q) \times X$. Then
--   $$\texttt{referenceJetEnvelopeWidths}\ \mathrm{stride}\ (\texttt{trimmedSpatialRootScale}\ \tau\ N\ \mathrm{stride})\ z = \tfrac52\,\tau\,N(z_2),$$
--   where `referenceJetEnvelopeWidths stride H z` $= 20\,\mathrm{stride}(z_2)\,H(z_2)$ and `trimmedSpatialRootScale τ N modulus x` $= \tau N(x)/8/\mathrm{modulus}(x)$ are explicit real-valued functions of OpenAI.
--
--   Lean: `OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_trimmed_s2`, which states OpenAI's `OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_trimmed` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedReferenceJetWindow.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B011` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedReferenceJetWindow.lean (declaration OAI.Erdos3.BooleanCubeKernel.referenceJetEnvelopeWidths_trimmed)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B011

section

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

theorem referenceJetEnvelopeWidths_trimmed_s2 {X : Type*} {q : ℕ}
    (stride N : X → ℕ) (hs : ∀ x, 0 < stride x) (τ : ℝ) (z : Option (Fin q) × X) :
    referenceJetEnvelopeWidths stride (trimmedSpatialRootScale τ N stride) z =
      (5 / 2 : ℝ) * τ * (N z.2 : ℝ) := by
  sorry

end Erdos3.BooleanCubeKernel

end

end OAI
end
