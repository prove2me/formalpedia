-- Prove2me | Theorems.Thm_LiouvilleFieldTheory_marginality_iff
-- name    : LiouvilleFieldTheory.marginality_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-01T10:01:59.643666+00:00
-- url     : https://prove2.me/theorems/24e37c1e-76f5-4335-bc05-39e83322d83f
-- title:
--   Marginality $\Delta(b) = 1 \iff Q = b + 1/b$
-- statement:
--   Let $b \in \mathbb{C}$ with $b \neq 0$ and let $Q \in \mathbb{C}$ be an arbitrary background charge. With the conformal dimension $\Delta(\alpha) = \alpha(Q - \alpha)$ of the field $e^{2\alpha\varphi}$, the field $e^{2b\varphi}$ in the action is marginal exactly when $Q$ is the Liouville background charge:
--   $$\Delta(b) = b\,(Q - b) = 1 \quad\Longleftrightarrow\quad Q = b + \frac{1}{b}.$$
--
--   This is the condition for conformal invariance of the Lagrangian formulation, which fixes the relation between the background charge and the coupling constant.
--
--   **Formalization Note** Here $Q$ is a free complex parameter (not the defined background charge), so the statement is the derivation of the relation $Q = b + 1/b$ from marginality.
-- source:
--   Wikipedia, "Liouville field theory", revision oldid=1376996606 (https://en.wikipedia.org/w/index.php?title=Liouville_field_theory&oldid=1376996606); section Conformal symmetry (p. 5): "the field e^{2bφ} ... must be marginal, i.e. have the conformal dimension Δ(b) = 1. This leads to the relation Q = b + 1/b".

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics
open Complex

namespace LiouvilleFieldTheory

theorem marginality_iff (b Q : ℂ) (hb : b ≠ 0) :
    b * (Q - b) = 1 ↔ Q = b + b⁻¹ := by
  sorry

end LiouvilleFieldTheory
