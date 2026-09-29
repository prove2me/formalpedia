-- Prove2me | Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaHBar_pos_and_le_relIndex
-- name    : ModularCurve.finrankAlong_heckeAlphaHBar_pos_and_le_relIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/5f0d8057-5a6b-5b9b-9ddc-d27c41ba24be
-- title:
--   Degree of X(Γ_H(M)∩Γ₀(Mt))→ X_H(M) is positive and bounded by the index
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $M$ be a nonzero natural number, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and let $t$ be a nonzero natural number. Write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M)\to(\mathbb{Z}/M)^\times$ sending a matrix to the reduction of its lower right entry. The map $\alpha=$ `heckeAlphaHBar L M H t` is the inclusion of intermediate fields, viewed as an $L$-algebra homomorphism, from `laurentBaseChange L (xHFunctionField M H)` into `laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * t))`, where `xHFunctionField M H` is the intermediate field `xHFunctionFieldC ℚ M H` of $\mathbb{Q}\subseteq\mathbb{Q}((q))$, where `xHTopFunctionFieldC ℚ M H (M * t)` is the field `qExpFunctionFieldC ℚ (Γ_H(M) ⊓ Γ₀(Mt))`, and where `laurentBaseChange L F₀` denotes the intermediate field of $L\subseteq L((q))$ generated over $L$ by the coefficientwise image of $F₀$ in $L((q))$. The assertion is that the rank `finrankAlong L α` of the target as a module over the source along $\alpha$ (which is $0$ by convention when that module is not finite) is strictly positive, and is at most the relative index of $\Gamma_H(M)\cap\Gamma_0(Mt)$ in $\Gamma_H(M)$. In particular the extension is finite.
--
--   This is the function-field form of the statement that the natural covering $X(\Gamma_H(M)\cap\Gamma_0(Mt))\to X_H(M)$ of modular curves has positive degree bounded by the index $[\Gamma_H(M):\Gamma_H(M)\cap\Gamma_0(Mt)]$, here over an arbitrary field of characteristic zero rather than over $\mathbb{C}$ alone. It supplies the finiteness needed to form norms along the Hecke correspondence, and is used in the computation of the norm of the second Hecke map on $q$-expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaHBar_pos_and_le_relIndex.lean

import Mathlib
import Definitions.Def_ModularCurve_XHHeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.finrankAlong_heckeAlphaHBar_pos_and_le_relIndex
    (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (t : ℕ) [NeZero t] :
    0 < AlgebraicCurve.finrankAlong L (ModularCurve.heckeAlphaHBar L M H t) ∧
      AlgebraicCurve.finrankAlong L (ModularCurve.heckeAlphaHBar L M H t) ≤
        (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * t)).relIndex (CohCarrier.GammaH M H) := by sorry
