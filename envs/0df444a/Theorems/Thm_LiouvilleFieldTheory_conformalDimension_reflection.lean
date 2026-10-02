-- Prove2me | Theorems.Thm_LiouvilleFieldTheory_conformalDimension_reflection
-- name    : LiouvilleFieldTheory.conformalDimension_reflection
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-01T09:43:31.785456+00:00
-- url     : https://prove2.me/theorems/7c86b8ee-0a8d-45f5-a307-0d23f1500ede
-- title:
--   Reflection invariance $\Delta(Q - \alpha) = \Delta(\alpha)$
-- statement:
--   Let $b \in \mathbb{C}$, $Q = b + 1/b$, and $\Delta(\alpha) = \alpha(Q - \alpha)$. For every momentum $\alpha \in \mathbb{C}$,
--   $$\Delta(Q - \alpha) = \Delta(\alpha).$$
--
--   Two energy eigenvectors whose momenta are related by the reflection $\alpha \to Q - \alpha$ are linearly dependent; this identity says that they carry the same conformal dimension, hence belong to the same representation.
--
--   **Formalization Note** No hypothesis on $b$ is needed; at $b = 0$ Lean uses $Q = 0$.
-- source:
--   Wikipedia, "Liouville field theory", revision oldid=1376996606 (https://en.wikipedia.org/w/index.php?title=Liouville_field_theory&oldid=1376996606); section Introduction (p. 1–2): reflection α → Q − α, Δ = α(Q − α).

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics
open Complex

namespace LiouvilleFieldTheory

theorem conformalDimension_reflection (b α : ℂ) :
    conformalDimension b (backgroundCharge b - α) = conformalDimension b α := by
  sorry

end LiouvilleFieldTheory
