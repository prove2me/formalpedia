-- Prove2me | Theorems.Thm_ModularCurve_exists_frickeAlgEquiv_xHFunctionFieldBar_galois_smul
-- name    : ModularCurve.exists_frickeAlgEquiv_xHFunctionFieldBar_galois_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/cf304a8d-d062-52fd-a055-c88c822ba83c
-- title:
--   Fricke involution on J_H(M) over ℚ̄
-- statement:
--   Let $M$ be a nonzero natural number and $H$ a subgroup of $(\mathbb{Z}/M)^\times$. Write $\bar F =$ `xHFunctionFieldBar M H` for the intermediate field of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the function field `xHFunctionField M H`, and $J_H =$ `JH M H` for the group $\mathrm{Pic}^0$ of degree-zero divisor classes of $\bar F$ over $\overline{\mathbb{Q}}$; an $\overline{\mathbb{Q}}$-algebra automorphism acts on $J_H$ through the semilinear automorphism pairing it with the identity of $\overline{\mathbb{Q}}$. The assertion is that there exists an $\overline{\mathbb{Q}}$-algebra automorphism $w$ of $\bar F$ with four properties. First, for every prime $\ell$, given integrality of the inclusion `heckeAlphaHBar` of $\bar F$ into the base-changed function field of level $\Gamma_H(M)\cap\Gamma_0(M\ell)$ and of the map `heckeBetaHBar` ($q\mapsto q^{\ell}$ where defined, and $\alpha$ otherwise), existence of principal divisors upstairs, and witnesses of the fundamental identity, of module-finiteness and of the pushforward norm formula along both maps, one has $T_\ell^{t}(w\cdot x) = w\cdot T_\ell x$ for all $x\in J_H$, where $T_\ell$ is the correspondence pullback-along-$\beta$ then pushforward-along-$\alpha$ and $T_\ell^{t}$ the one with $\alpha,\beta$ interchanged. Second, $\langle d\rangle\bigl(w\cdot \langle d\rangle x\bigr) = w\cdot x$ for all $d\in(\mathbb{Z}/M)^\times$ and $x$, where $\langle d\rangle =$ `diamondHBar M H d`. Third, $w\cdot(w\cdot x) = x$. Fourth, for every $\sigma\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and every natural number $c$ coprime to $M$ with $\sigma\zeta=\zeta^{c}$ for all $\zeta$ satisfying $\zeta^{M}=1$, one has $w\cdot(\sigma\cdot x) = \sigma\cdot\langle c\rangle(w\cdot x)$ for all $x\in J_H$.
--
--   This packages the Atkin–Lehner laws for the Fricke involution $w_M$ of $X_H(M)$, acting on degree-zero divisor classes: it conjugates the Hecke correspondence into its transpose, inverts the diamond operators, is an involution, and satisfies the reciprocity law describing its failure to be defined over $\mathbb{Q}$ in terms of the cyclotomic character and the diamond action. It is used in the analysis of the Galois action on the Tate module of $J_H$ and in the corresponding statement for $X_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_frickeAlgEquiv_xHFunctionFieldBar_galois_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_frickeAlgEquiv_xHFunctionFieldBar_galois_smul (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) :
    ∃ w : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      (∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
          (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
          (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hfinβ)
          (x : JH M H),
        heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w • heckePic0HBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : (ZMod M)ˣ) (x : JH M H),
        diamondHBar M H d (SemilinearAut.ofAlgAut w • diamondHBar M H d x)
          = SemilinearAut.ofAlgAut w • x) ∧
      (∀ x : JH M H, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x : JH M H,
            SemilinearAut.ofAlgAut w • (σ • x)
              = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w • x)) := by sorry
