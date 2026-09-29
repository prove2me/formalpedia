-- Prove2me | Theorems.Thm_ModularCurve_frickeAlgEquiv_pic0_laws_of_slash_fricke_of_galois_smul
-- name    : ModularCurve.frickeAlgEquiv_pic0_laws_of_slash_fricke_of_galois_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/f07947e5-f629-5ce8-8a51-2bd800375c52
-- title:
--   Fricke laws on Pic⁰ of X_H(M), pinned by slash and Galois clauses
-- statement:
--   Let $M\ge 1$ and let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$; write $\bar{\mathbb{Q}}\cdot F_H$ for `xHFunctionFieldBar M H`, the intermediate field of $\bar{\mathbb{Q}}((q))$ generated over $\bar{\mathbb{Q}}$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_H(M)$ (itself generated over $\mathbb{Q}$ by ratios of integral modular forms on $\Gamma_H(M)$), and $J_H = \operatorname{Pic}^0$ of that field over $\bar{\mathbb{Q}}$. Fix a ring homomorphism $\iota : \bar{\mathbb{Q}}\to\mathbb{C}$, an element $W\in \mathrm{GL}_2(\mathbb{R})$ whose matrix is $\begin{pmatrix}0&-1\\M&0\end{pmatrix}$, and a $\bar{\mathbb{Q}}$-algebra automorphism $w$ of $\bar{\mathbb{Q}}\cdot F_H$ subject to two clauses: (i) for all $x$, all $k\in\mathbb{Z}$ and all weight-$k$ modular forms $f,g$ on $\Gamma_H(M)$, if the $\iota$-image of $x$ times the $q$-expansion of $g$ equals that of $f$ in $\mathbb{C}((q))$, then the $\iota$-image of $wx$ times the $q$-expansion of $g\mid_k W$ equals that of $f\mid_k W$; (ii) for every $\sigma\in\operatorname{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ and every $c$ coprime to $M$ with $\sigma\zeta=\zeta^c$ on $M$-th roots of unity, $w(\sigma\cdot x)=\sigma\cdot\langle c\rangle^{*}(wx)$, where $\sigma$ acts coefficientwise and $\langle c\rangle^{*}$ is `diamondAutHBar`. Then, with $w$ acting on $J_H$ through the semilinear automorphism `SemilinearAut.ofAlgAut w` (trivial on $\bar{\mathbb{Q}}$), four laws hold: (1) for every prime $\ell$, given integrality of the degeneracy maps $\alpha$ (inclusion) and $\beta$ ($q\mapsto q^{\ell}$ substitution when it lands in the level-$M\ell$ field, else $\alpha$) into the base-changed function field of $\Gamma_H(M)\cap\Gamma_0(M\ell)$, together with principal-divisor, fundamental-identity, finiteness and norm-formula hypotheses along $\alpha$ and $\beta$, the transposed Hecke correspondence applied to $w\cdot x$ equals $w$ applied to the Hecke correspondence of $x$; (2) $\langle d\rangle (w\cdot \langle d\rangle x)=w\cdot x$ for all $d\in(\mathbb{Z}/M)^\times$; (3) $w\cdot(w\cdot x)=x$; (4) $w\cdot(\sigma\cdot x)=\sigma\cdot\langle c\rangle(w\cdot x)$ for $\sigma,c$ as in (ii).
--
--   This is the Fricke involution $w_M$ on the Jacobian of $X_H(M)$ over $\bar{\mathbb{Q}}$, together with its standard relations: it conjugates the Hecke correspondence into its transpose, inverts the diamond operators, is an involution, and intertwines the Galois action with a diamond twist. Unlike an existence statement, the result is keyed on a given $w$ pinned by the slash clause (i) and the Galois clause (ii), so that the same $w$ can be reused downstream; it is cited in the analysis of the Néron model of $J_H$ at $p$, for the construction of idempotent pairings on corners and for counting toric points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frickeAlgEquiv_pic0_laws_of_slash_fricke_of_galois_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open ModularCurve
open scoped MatrixGroups ModularForm

theorem ModularCurve.frickeAlgEquiv_pic0_laws_of_slash_fricke_of_galois_smul (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ)
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0])

    (w : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hw₁ : ∀ (x : ↥(xHFunctionFieldBar M H)) (k : ℤ)
        (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
        coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
        coeffMap ι ((w x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W)))
    (hw₂ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ x : ↥(xHFunctionFieldBar M H),
          w (arithmeticGalois (xHFunctionField M H) σ • x) =
            arithmeticGalois (xHFunctionField M H) σ • diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x)) :
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
