-- Prove2me | Theorems.Thm_ModularCurve_heckePic0Bar_smul
-- name    : ModularCurve.heckePic0Bar_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/2c0ac81a-ce37-5572-bb7f-47e1685f4af4
-- title:
--   Galois equivariance of the Hecke correspondence on Pic⁰
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure and let $N,\ell$ be nonzero natural numbers. Write $F_M =$ `modularFunctionFieldFull M` for the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions attached to $M$, and $L\cdot F_M =$ `laurentBaseChange L F_M` for the subfield of $L((q))$ generated over $L$ by the coefficientwise image of $F_M$. Two $L$-algebra maps $L\cdot F_N \to L\cdot F_{N\ell}$ are in play: $\alpha =$ `heckeAlphaBar L N ℓ`, the inclusion coming from $N \mid N\ell$, and $\beta =$ `heckeBetaBar L N ℓ`, induced by $q \mapsto q^{\ell}$. The hypotheses are: $h_\alpha$ and $h_\beta$, integrality of the underlying ring homomorphisms of $\alpha$ and $\beta$; the property that every nonzero element of $L\cdot F_{N\ell}$ has a divisor of degree $0$ supported on the places over $L$; $h_{FI}$, the fundamental identity for the extension $L\cdot F_{N\ell}/L\cdot F_N$ taken along $\beta$; $h_{\mathrm{fin}}$, finiteness of $L\cdot F_{N\ell}$ as a module over $L\cdot F_N$ along $\alpha$; and $h_N$, the pushforward norm formula for divisors along $\alpha$. Then for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $L$ and every class $c$ in $\mathrm{Pic}^0$ of $L\cdot F_N$ over $L$ (degree-zero divisors modulo principal ones), the endomorphism `heckePic0Bar` of that $\mathrm{Pic}^0$ — the correspondence obtained by pulling back along $\beta$ and pushing forward along $\alpha$, descended to degree-zero divisor classes — satisfies `heckePic0Bar` $(\sigma \cdot c) = \sigma \cdot$ `heckePic0Bar` $(c)$, where $\sigma$ acts on $\mathrm{Pic}^0$ through the coefficientwise action on $L\cdot F_N$.
--
--   For $\ell$ prime this is the statement that the Hecke correspondence $\alpha_*\circ\beta^*$, classically $T_\ell$ on the Jacobian of the modular curve of level $N$, commutes with the action of $\mathrm{Aut}(L/\mathbb{Q})$ on divisor classes, reflecting the fact that the modular correspondences are defined over $\mathbb{Q}$. It is used to equip the degree-zero Picard group with compatible Hecke and Galois actions, in particular by [`ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar`](thm.html#ModularCurve.smulCommClass_JZero_of_heckeOperatorsCommuteBar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckePic0Bar_smul.lean

import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.heckePic0Bar_smul {L : Type*} [Field L] [Algebra ℚ L] {N ℓ : ℕ} [NeZero N] [NeZero ℓ] (hα : ModularCurve.HeckeAlphaBarIntegral L N ℓ) (hβ : ModularCurve.HeckeBetaBarIntegral L N ℓ) [AlgebraicCurve.HasPrincipalDivisors L (ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (N * ℓ)))] (hFI : AlgebraicCurve.FundamentalIdentityAlong L (ModularCurve.heckeBetaBar L N ℓ) hβ) (hfin : AlgebraicCurve.FiniteAlong L (ModularCurve.heckeAlphaBar L N ℓ)) (hN : AlgebraicCurve.NormFormulaAlong L (ModularCurve.heckeAlphaBar L N ℓ) hfin) (σ : L ≃ₐ[ℚ] L) (c : AlgebraicCurve.Pic0 L (ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull N))) : ModularCurve.heckePic0Bar hα hβ hFI hfin hN (σ • c) = σ • ModularCurve.heckePic0Bar hα hβ hFI hfin hN c := by sorry
