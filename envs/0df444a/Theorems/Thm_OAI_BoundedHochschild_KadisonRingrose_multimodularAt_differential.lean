-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_multimodularAt_differential
-- name    : OAI.BoundedHochschild.KadisonRingrose.multimodularAt_differential
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:10.33533+00:00
-- url     : https://prove2.me/theorems/58819b84-ddac-4fcf-810b-ad5ff177a2ba
-- title:
--   The differential preserves multimodularity at an element
-- statement:
--   Let $M$ be a unital C*-algebra, $f$ a bounded $(n+1)$-linear map $M^{n+1}\to M$ and $r\in M$. Say $f$ is multimodular at $r$ (`MultimodularAt f r`) if $f(rx_0,x_1,\dots)=rf(x)$, $f(\dots,x_nr)=f(x)r$ and $f(\dots,x_jr,x_{j+1},\dots)=f(\dots,x_j,rx_{j+1},\dots)$ for all $j$. If $f$ is multimodular at $r$, then so is its Hochschild differential `differential f`.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.multimodularAt_differential`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/MultimodularEndFaces.lean#L91

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

theorem multimodularAt_differential {n : ℕ} (f : Cochain M (n + 1)) (r : M)
    (hf : MultimodularAt f r) : MultimodularAt (differential f) r := by
  sorry

end BoundedHochschild.KadisonRingrose
end
end OAI
