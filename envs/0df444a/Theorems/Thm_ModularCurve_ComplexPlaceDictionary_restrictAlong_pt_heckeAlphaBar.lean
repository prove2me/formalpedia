-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeAlphaBar
-- name    : ModularCurve.ComplexPlaceDictionary.restrictAlong_pt_heckeAlphaBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/868068a8-1778-5e81-ab7f-bb4d9308b74b
-- title:
--   Degeneracy inclusion restricts the place of τ to the place of τ
-- statement:
--   Let $N \ge 1$ and $\ell \ge 1$ be natural numbers. For a level $M \ge 1$ write $\mathbb{C}F_M$ for the intermediate field [`ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull M)`](def/ModularCurve_LaurentCoeff.html#L103) of $\mathbb{C}((q))$, and let $\alpha =$ [`ModularCurve.heckeAlphaBar ℂ N ℓ`](def/ModularCurve_HeckeOperator.html#L66) be the $\mathbb{C}$-algebra inclusion $\mathbb{C}F_N \hookrightarrow \mathbb{C}F_{N\ell}$ coming from the containment of these subfields of $\mathbb{C}((q))$, so $\alpha$ leaves the underlying Laurent series unchanged. Let $D$ be a complex place dictionary at level $N$ and $D'$ one at level $N\ell$; such a dictionary at level $M$ consists of a map $\tau \mapsto P_\tau$ from the upper half plane to places of $\mathbb{C}F_M$ over $\mathbb{C}$ together with positive integers $e_\tau$, subject to $\Gamma_0(M)$-invariance $P_{\gamma\tau} = P_\tau$, to the requirement that $x$ lie in the valuation ring of $P_\tau$ exactly when $z \mapsto \lVert \mathrm{realize}_M(x)(z)\rVert$ is bounded on a punctured neighbourhood of $\tau$, and to the order formula $\mathrm{ord}_\tau(\mathrm{realize}_M(x)) = e_\tau \cdot \mathrm{ord}_{P_\tau}(x)$ for $x \neq 0$. Assume the ring homomorphism underlying $\alpha$ is integral ([`ModularCurve.HeckeAlphaBarIntegral ℂ N ℓ`](def/ModularCurve_HeckeOperator.html#L124)), and let $\tau$ be a point of the upper half plane. Then the restriction of the place $D'.\mathrm{pt}\,\tau$ along $\alpha$, that is the place of $\mathbb{C}F_N$ whose valuation ring is the preimage under $\alpha$ of that of $D'.\mathrm{pt}\,\tau$, equals $D.\mathrm{pt}\,\tau$. No compatibility between $D$ and $D'$ is assumed.
--
--   This is the statement that the first degeneracy map $X_0(N\ell) \to X_0(N)$, realised on function fields as the inclusion of $q$-expansion fields, sends the point of the upper half plane $\tau$ viewed at level $N\ell$ to the same $\tau$ viewed at level $N$. It is used in the computation of the Hecke correspondence on divisors, through [`ModularCurve.ComplexPlaceDictionary.heckeDivBar_single_pt`](thm.html#ModularCurve.ComplexPlaceDictionary.heckeDivBar_single_pt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeAlphaBar.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.ComplexPlaceDictionary.restrictAlong_pt_heckeAlphaBar
    {N : ℕ} [NeZero N] (ℓ : ℕ) [NeZero ℓ] (D : ModularCurve.ComplexPlaceDictionary N)
    (D' : ModularCurve.ComplexPlaceDictionary (N * ℓ))
    (hα : ModularCurve.HeckeAlphaBarIntegral ℂ N ℓ) (τ : UpperHalfPlane) :
    (D'.pt τ).restrictAlong (ModularCurve.heckeAlphaBar ℂ N ℓ) hα = D.pt τ := by sorry
