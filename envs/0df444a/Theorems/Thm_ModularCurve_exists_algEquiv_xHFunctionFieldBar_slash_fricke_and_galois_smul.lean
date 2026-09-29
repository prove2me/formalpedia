-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul
-- name    : ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/0dc509de-7f67-529c-a37a-14455bff898c
-- title:
--   Fricke pull-back on ℚ̄· F(Γ_H(M)) and its Galois twist
-- statement:
--   Let $M$ be a nonzero natural number and $H \le (\mathbb{Z}/M)^{\times}$ a subgroup, and write $\Gamma_H(M)$ for the congruence subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $\Gamma_0(M)$ whose elements have lower-right entry reducing into $H$ mod $M$, regarded inside $\mathrm{GL}_2(\mathbb{R})$. Write $F_H =$ [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79), an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$, and $\overline{F}_H =$ [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123), the intermediate field of $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` by the coefficientwise image of $F_H$. Assume (hypothesis `hin`) that every $d \in (\mathbb{Z}/M)^{\times}$ admits a $\overline{\mathbb{Q}}$-algebra automorphism $\sigma$ of $\overline{F}_H$ with [`ModularCurve.IsDiamondAutHBar M H d σ`](def/ModularCurve_XHOperators.html#L18): for all weights $k$, all modular forms $f,g$ of weight $k$ on $\Gamma_H(M)$ whose $q$-expansions (width $1$) come from integral power series $p_f,p_g$ with `intSeriesC ℚ pg ≠ 0`, and all $\gamma \in \Gamma_0(M)$ with upper-left entry $\equiv d \pmod M$, the value of $\sigma$ at the element of $\overline{F}_H$ given by $p_f/p_g$ is the coefficientwise image of some $y \in F_H$ satisfying $y \cdot q\text{-exp}(g\mid_k\gamma) = q\text{-exp}(f\mid_k\gamma)$ in $\mathbb{C}((q))$. Finally fix a ring embedding $\iota : \overline{\mathbb{Q}} \to \mathbb{C}$ and $W \in \mathrm{GL}_2(\mathbb{R})$ with matrix $\begin{pmatrix} 0 & -1 \\ M & 0\end{pmatrix}$. The conclusion is that there exists a $\overline{\mathbb{Q}}$-algebra automorphism $w$ of $\overline{F}_H$ such that: (1) for every $x \in \overline{F}_H$, every $k \in \mathbb{Z}$ and all modular forms $f,g$ of weight $k$ on $\Gamma_H(M)$, if $\iota(x)\cdot q\text{-exp}(g) = q\text{-exp}(f)$ then $\iota(w\,x) \cdot q\text{-exp}(g\mid_k W) = q\text{-exp}(f\mid_k W)$, where $\iota$ is applied to Laurent coefficients and power series are embedded into $\mathbb{C}((q))$; and (2) for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every natural number $c$ coprime to $M$ with $\sigma\zeta = \zeta^{c}$ for all $\zeta$ with $\zeta^{M}=1$, and every $x \in \overline{F}_H$, one has $w(\sigma \cdot x) = \sigma \cdot \big(\langle c\rangle (w\,x)\big)$, where $\sigma$ acts coefficientwise through [`ModularCurve.arithmeticGalois`](def/ModularCurve_ArithmeticGalois.html#L54) and $\langle c \rangle =$ [`ModularCurve.diamondAutHBar M H`](def/ModularCurve_XHOperators.html#L32) applied to the unit of $\mathbb{Z}/M$ determined by $c$.
--
--   This is the existence of the Fricke pull-back $w_M$ as an automorphism of the $\overline{\mathbb{Q}}$-function field of the $\infty$-rational model of $X_H(M)$, together with Shimura's reciprocity law at $W$: conjugating $w_M$ by the arithmetic Galois action twists it by the diamond operator $\langle c \rangle$ attached to the cyclotomic character value $c$. It is used in the construction of the Fricke-conjugated Hecke operators on $X_H(M)$ and in the analysis of the Jacobian and its Néron model at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul (M : ℕ)
    [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hin : ∀ d : (ZMod M)ˣ, ∃ σ : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ]
      ModularCurve.xHFunctionFieldBar M H, ModularCurve.IsDiamondAutHBar M H d σ)
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ w : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.xHFunctionFieldBar M H,
      (∀ (x : ModularCurve.xHFunctionFieldBar M H) (k : ℤ)
          (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
          ModularCurve.coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
          ModularCurve.coeffMap ι ((w x : ModularCurve.xHFunctionFieldBar M H) :
                LaurentSeries (AlgebraicClosure ℚ)) *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W))) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x : ModularCurve.xHFunctionFieldBar M H,
            w (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ • x) =
              ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ •
                ModularCurve.diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x)) := by sorry
