-- Prove2me | Theorems.Thm_LiouvilleFieldTheory_conformalDimension_momentum
-- name    : LiouvilleFieldTheory.conformalDimension_momentum
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T10:08:50.715363+00:00
-- url     : https://prove2.me/theorems/02efdcd0-e79a-484b-bd22-50e6977ac88b
-- title:
--   $\Delta(Q/2 + iP) = \frac{c-1}{24} + P^2$
-- statement:
--   Let $b \in \mathbb{C}$, $Q = b + 1/b$, $c = 1 + 6Q^2$, and $\Delta(\alpha) = \alpha(Q - \alpha)$. For every $P \in \mathbb{C}$,
--   $$\Delta\!\left(\frac{Q}{2} + iP\right) = \frac{c - 1}{24} + P^2.$$
--
--   This expresses the conformal dimension of a state of the continuous spectrum in terms of its momentum $P$; for real $P$ it shows $\Delta \in \frac{c-1}{24} + \mathbb{R}_+$.
--
--   **Formalization Note** The identity is stated for all complex $P$ (the source uses $P \in \mathbb{R}_+$) and all $b \in \mathbb{C}$.
-- source:
--   Wikipedia, "Liouville field theory", revision oldid=1376996606 (https://en.wikipedia.org/w/index.php?title=Liouville_field_theory&oldid=1376996606); section Spectrum (p. 2): Δ ∈ (c−1)/24 + ℝ₊ ⟺ α ∈ Q/2 + iP, P ∈ ℝ₊.

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics
open Complex

namespace LiouvilleFieldTheory

theorem conformalDimension_momentum (b P : ℂ) :
    conformalDimension b (backgroundCharge b / 2 + I * P) =
      (centralCharge b - 1) / 24 + P ^ 2 := by
  sorry

end LiouvilleFieldTheory
