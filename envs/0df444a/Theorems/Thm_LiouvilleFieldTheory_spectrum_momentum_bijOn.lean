-- Prove2me | Theorems.Thm_LiouvilleFieldTheory_spectrum_momentum_bijOn
-- name    : LiouvilleFieldTheory.spectrum_momentum_bijOn
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-01T11:13:44.18933+00:00
-- url     : https://prove2.me/theorems/2e3d83ec-4e4e-4817-9c81-d6320aa139aa
-- title:
--   Liouville spectrum: $\alpha = Q/2 + iP$, $P \in \mathbb{R}_+$, parametrizes $\Delta \in \frac{c-1}{24} + \mathbb{R}_+$
-- statement:
--   Let $b \in \mathbb{C}$ be the coupling constant of Liouville theory, $Q = b + 1/b$ the background charge, $c = 1 + 6Q^2$ the central charge, and $\Delta(\alpha) = \alpha(Q - \alpha)$ the conformal dimension of the primary field of momentum $\alpha$.
--
--   The spectrum of Liouville theory consists of the conformal dimensions $\Delta \in \frac{c-1}{24} + \mathbb{R}_+$, which in terms of the momentum amounts to $\alpha \in \frac{Q}{2} + i\,\mathbb{R}_+$. Precisely, the map
--   $$P \;\longmapsto\; \Delta\!\left(\tfrac{Q}{2} + iP\right)$$
--   is a bijection from $\mathbb{R}_+ = [0, \infty)$ onto
--   $$\frac{c-1}{24} + \mathbb{R}_+ = \left\{\tfrac{c-1}{24} + t \;:\; t \in \mathbb{R},\ t \ge 0\right\} \subset \mathbb{C}.$$
--
--   This is the statement that the half-line of momenta $P \ge 0$ labels each representation of the continuous spectrum exactly once; the reflection $\alpha \to Q - \alpha$ is responsible for the momentum taking values on a half-line rather than a full line.
--
--   **Formalization Note** $b$ ranges over all of $\mathbb{C}$ (the identity also holds with Lean's junk value at $b = 0$), and $\mathbb{R}_+$ is taken to include $0$, i.e. $P = 0$ corresponds to the bottom $\Delta = \frac{c-1}{24}$ of the spectrum.
-- source:
--   Wikipedia, "Liouville field theory", revision oldid=1376996606 (https://en.wikipedia.org/w/index.php?title=Liouville_field_theory&oldid=1376996606); section Spectrum (p. 2): "The conformal dimension takes values Δ ∈ (c−1)/24 + ℝ₊, which in terms of the momentum α amounts to α ∈ Q/2 + iP with P ∈ ℝ₊".

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics
open Complex

namespace LiouvilleFieldTheory

theorem spectrum_momentum_bijOn (b : ℂ) :
    Set.BijOn (fun P : ℝ => conformalDimension b (backgroundCharge b / 2 + I * P))
      (Set.Ici 0)
      {Δ : ℂ | ∃ t : ℝ, 0 ≤ t ∧ Δ = (centralCharge b - 1) / 24 + t} := by
  sorry

end LiouvilleFieldTheory
