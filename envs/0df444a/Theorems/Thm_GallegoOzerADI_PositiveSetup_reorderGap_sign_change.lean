-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_reorderGap_sign_change
-- name    : GallegoOzerADI.PositiveSetup.reorderGap_sign_change
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:48:54.772124+00:00
-- url     : https://prove2.me/theorems/a94c68d9-c808-4309-8510-9a148c47a169
-- title:
--   Lemma 2 — $H$ has a unique sign change from $-$ to $+$
-- statement:
--   Let $K > 0$ and let $V : \mathbb{R} \to \mathbb{R}$ satisfy
--
--   1. $V \in C(0, K)$;
--   2. $V$ has a finite global minimizer $S$;
--   3. there is $x < S$ with $V(x) > K + V(S)$.
--
--   Let $H(x) = K + \min_{y \ge x} V(y) - V(x)$. Then $H$ has a unique sign change from $-$ to $+$: $H$ takes a negative value, $H$ takes a positive value, and $H$ never passes from a positive to a negative value, i.e.
--
--   $$
--   x_1 < x_2,\ H(x_1) > 0 \implies H(x_2) \ge 0.
--   $$
--
--   Consequently the inventory positions from which ordering is strictly profitable lie entirely to the left of those from which it is strictly unprofitable. This is the structural fact behind the $(s,S)$ form of the optimal policy (Corollary 1, Theorem 1).
--
--   **Formalization Note** The paper states the lemma for $V_t(\cdot, o_t)$ at a fixed period $t$ and observed-demand vector $o_t$; it is formalized for an arbitrary function $V$ and constant $K$, which is what the lemma uses. $K > 0$ is the standing assumption of Section 4 (positive set-up costs). "A unique sign change" is formalized in the usual sense of counting sign changes, where zeros are not counted: negative somewhere, positive somewhere, and no positive value followed by a negative one. The minimum over $y \ge x$ is an infimum; it is finite because $V$ has a global minimizer.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1350, Lemma 2 (proof p. 1358)

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost

namespace GallegoOzerADI.PositiveSetup

theorem reorderGap_sign_change (K : ℝ) (hK : 0 < K) (V : ℝ → ℝ) (hV : ABConvex 0 K V)
    (S : ℝ) (hS : ∀ x, V S ≤ V x) (hiii : ∃ x, x < S ∧ K + V S < V x) :
    (∃ x, reorderGap K V x < 0) ∧ (∃ x, 0 < reorderGap K V x) ∧
      ∀ x₁ x₂, x₁ < x₂ → 0 < reorderGap K V x₁ → 0 ≤ reorderGap K V x₂ := by sorry

end GallegoOzerADI.PositiveSetup
