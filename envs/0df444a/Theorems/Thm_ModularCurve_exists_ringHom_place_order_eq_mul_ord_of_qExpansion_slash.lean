-- Prove2me | Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
-- name    : ModularCurve.exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/b76d6a0e-7f9a-55a8-851c-7490ecf00916
-- title:
--   Cuspidal place and q_N-expansion at σ∞ on X(Γ)
-- statement:
--   Let $\Gamma\le\mathrm{SL}_2(\mathbb Z)$ be a subgroup of finite index containing $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$, let $F_0$ be an intermediate field of $\mathbb Q\subseteq\mathbb Q((q))$ equal to [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101), the subfield generated over $\mathbb Q$ by the Laurent series $\mathrm{int}(p_f)/\mathrm{int}(p_g)$ attached to integral $q$-expansions $p_f,p_g$ of modular forms $f,g$ of some weight $k$ for $\Gamma$ with $\mathrm{int}(p_g)\ne 0$, and let $\sigma\in\mathrm{SL}_2(\mathbb Z)$. Write $E=\mathbb C\cdot F_0\subseteq\mathbb C((q))$ for `laurentBaseChange ℂ F₀`, the subfield of $\mathbb C((q))$ generated over $\mathbb C$ by the coefficientwise image of $F_0$, and $N=[\mathrm{SL}_2(\mathbb Z):\mathrm{core}\,\Gamma]$ the index of the normal core of $\Gamma$. The assertion is that there exist a ring homomorphism $\Phi\colon E\to\mathbb C((q))$, a place $P$ of $E$ over $\mathbb C$ (a proper valuation subring of $E$ containing $\mathbb C$ and a principal ideal ring), and a natural number $e>0$ such that: (i) $x$ lies in the valuation ring $\mathcal O_P$ iff $\mathrm{ord}\,\Phi(x)\ge 0$, and also iff the level-$\Gamma$ realisation $\tau\mapsto x(\sigma\tau)$ on $\mathfrak H$ (defined as $g/h$ for a presentation $x\cdot\widetilde h=\widetilde g$ by $q$-expansions of period $1$, and $0$ if none exists) tends to a finite limit as $\operatorname{Im}\tau\to\infty$; (ii) for every such presentation $x\cdot\widetilde h=\widetilde g$ with $g,h\in M_k(\Gamma)$, $h\ne0$, one has $\Phi(x)\cdot\widetilde{h\mid_k\sigma}=\widetilde{g\mid_k\sigma}$, the expansions now taken with period $N$; (iii) $\Phi$ sends each constant $c\in\mathbb C$ to the constant Laurent series $c$; (iv) $\mathrm{ord}\,\Phi(x)=e\cdot\mathrm{ord}_P(x)$ for all $x\ne0$, where $\mathrm{ord}_P$ is minus the logarithm of the adic valuation of $\mathcal O_P$; (v) any $y\in E$ whose underlying series is `jqModC ℂ` satisfies $\mathrm{ord}\,\Phi(y)=e\cdot\mathrm{ord}_P(y)=-N$ and $y\notin\mathcal O_P$; and (vi) for every $x\ne0$ there is $L\ne0$ with $x(\sigma\tau)\,\exp\!\left(-2\pi i\,e\,\mathrm{ord}_P(x)\,\tau/N\right)\to L$ as $\operatorname{Im}\tau\to\infty$.
--
--   This is the analytic half of the cusp dictionary for the modular curve attached to $\Gamma$: $P$ is the cuspidal place at $\sigma\infty$, at which $j$ has a pole of order $N$, $e$ measures the ramification of the parameter $q_N$ over a local parameter at $P$, and orders at $P$ are read off as leading exponents of $q_N$-expansions, with the leading coefficient of the realisation recorded as a nonzero limit. It feeds the computation of $\mathrm{ord}_P$ in terms of cusp widths and the asymptotic behaviour of realisations of functions with a pole at $P$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (σ : SL(2, ℤ)) :
    ∃ (Φ : ModularCurve.laurentBaseChange ℂ F₀ →+* LaurentSeries ℂ)
      (P : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀)) (e : ℕ),
      0 < e ∧
      (∀ x : ModularCurve.laurentBaseChange ℂ F₀, x ∈ P.toValuationSubring ↔ 0 ≤ (Φ x).order) ∧
      (∀ x : ModularCurve.laurentBaseChange ℂ F₀, x ∈ P.toValuationSubring ↔
        ∃ L : ℂ, Filter.Tendsto
          (fun τ : UpperHalfPlane => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (σ • τ)) atImInfty (𝓝 L)) ∧
      (∀ (x : ModularCurve.laurentBaseChange ℂ F₀) (k : ℤ)
          (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k), h ≠ 0 →
        (x : LaurentSeries ℂ) *
            ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) →
        Φ x * ((UpperHalfPlane.qExpansion (Γ.normalCore.index : ℝ)
              ((h : UpperHalfPlane → ℂ) ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((UpperHalfPlane.qExpansion (Γ.normalCore.index : ℝ)
              ((g : UpperHalfPlane → ℂ) ∣[k] σ) : PowerSeries ℂ) : LaurentSeries ℂ)) ∧
      (∀ c : ℂ, Φ (algebraMap ℂ (ModularCurve.laurentBaseChange ℂ F₀) c) = HahnSeries.C c) ∧
      (∀ x : ModularCurve.laurentBaseChange ℂ F₀, x ≠ 0 → (Φ x).order = e * P.ord x) ∧
      (∀ y : ModularCurve.laurentBaseChange ℂ F₀, (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ →
        (Φ y).order = -(Γ.normalCore.index : ℤ) ∧ (e : ℤ) * P.ord y = -(Γ.normalCore.index : ℤ) ∧
          y ∉ P.toValuationSubring) ∧
      (∀ x : ModularCurve.laurentBaseChange ℂ F₀, x ≠ 0 → ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto
          (fun τ : UpperHalfPlane => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (σ • τ) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((e : ℤ) * P.ord x : ℂ) * (τ : ℂ) / (Γ.normalCore.index : ℂ))))
          atImInfty (𝓝 L)) := by sorry
