-- Prove2me | Theorems.Thm_ModularCurve_heckePic0HBarTranspose_smul_diamondHBar_smul_smul_of_qExpansion_slash_fricke
-- name    : ModularCurve.heckePic0HBarTranspose_smul_diamondHBar_smul_smul_of_qExpansion_slash_fricke
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/a3b4a0fa-1f13-57a5-9368-917851bf5558
-- title:
--   Fricke automorphism transposes Hecke operators and inverts diamonds
-- statement:
--   Fix $M\ge 1$, a subgroup $H\le(\mathbb Z/M)^\times$, a ring homomorphism $\iota:\overline{\mathbb Q}\to\mathbb C$, and $W\in \mathrm{GL}_2(\mathbb R)$ whose matrix is $\begin{pmatrix}0&-1\\M&0\end{pmatrix}$. Let $\bar F_H=$ `xHFunctionFieldBar M H`, the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of the field of ratios of integral $q$-expansions of modular forms on $\Gamma_H(M)$, and let $J_H=\mathrm{Pic}^0(\overline{\mathbb Q},\bar F_H)$. Let $w$ be a $\overline{\mathbb Q}$-algebra automorphism of $\bar F_H$ satisfying: for every $x\in\bar F_H$, every $k\in\mathbb Z$ and all modular forms $f,g$ of weight $k$ on $\Gamma_H(M)$, if $\iota_*(x)\cdot q\text{-exp}(g)=q\text{-exp}(f)$ in $\mathbb C((q))$ then $\iota_*(w(x))\cdot q\text{-exp}(g\mid_k W)=q\text{-exp}(f\mid_k W)$. Write $w_*$ for the action on $J_H$ of the semilinear automorphism $(w,1)$. Then three assertions hold. First, for every prime $\ell$, given witnesses that the degeneracy maps $\alpha$ (inclusion) and $\beta$ ($q\mapsto q^\ell$, replaced by $\alpha$ when that substitution leaves the level-$M\ell$ field) from $\bar F_H$ to the base-changed function field of $\Gamma_H(M)\cap\Gamma_0(M\ell)$ are integral, that this larger field has principal divisors of degree zero, and of the fundamental identity, finiteness and pushforward norm formula along each of $\alpha,\beta$, the transposed Hecke correspondence (pullback along $\alpha$ then pushforward along $\beta$) applied to $w_*x$ equals $w_*$ of the Hecke correspondence (pullback along $\beta$ then pushforward along $\alpha$) applied to $x$, for all $x\in J_H$. Second, for every $d\in(\mathbb Z/M)^\times$ and $x\in J_H$, $\langle d\rangle_*(w_*(\langle d\rangle_* x))=w_*x$, where $\langle d\rangle_*$ is the action on $J_H$ of the diamond automorphism attached to $d$. Third, $w_*(w_*x)=x$ for all $x\in J_H$.
--
--   These are the Atkin–Lehner–Li commutation laws for the Fricke involution on the Jacobian of $X_H(M)$: the Fricke automorphism interchanges each Hecke correspondence with its transpose, conjugates a diamond operator into its inverse, and is an involution. The statement isolates the implication from the $q$-expansion specification of the Fricke automorphism to these laws, and is used in assembling the simultaneous Fricke data for $X_1(M)$ and $X_H(M)$ together with their Galois equivariance and compatibility with the degeneracy maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckePic0HBarTranspose_smul_diamondHBar_smul_smul_of_qExpansion_slash_fricke.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve
open ModularCurve
open scoped MatrixGroups ModularForm

theorem ModularCurve.heckePic0HBarTranspose_smul_diamondHBar_smul_smul_of_qExpansion_slash_fricke
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ι : AlgebraicClosure ℚ →+* ℂ)
    (W : GL (Fin 2) ℝ) (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0])
    (w : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H)
    (hw : ∀ (x : xHFunctionFieldBar M H) (k : ℤ)
        (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
        ModularCurve.coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
        ModularCurve.coeffMap ι ((w x : xHFunctionFieldBar M H) :
              LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W))) :
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
    (∀ x : JH M H, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) := by sorry
