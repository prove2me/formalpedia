-- Prove2me | Theorems.Thm_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p
-- name    : ModularCurve.XOneP.comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/a207cb08-2b17-5f3c-acf0-5a2c6cd9109e
-- title:
--   Atkin–Lehner pull-back at p swaps the degeneracy embeddings
-- statement:
--   Fix a prime $p$ and $M \ge 1$ with $p \nmid M$, integers $y, w_0$ with $p w_0 - My = 1$, and matrices $\gamma, \gamma' \in \mathrm{SL}_2(\mathbb Z)$ given by $\gamma = \begin{pmatrix} 1 & y \\ M & p w_0\end{pmatrix}$ and $\gamma' = \begin{pmatrix} w_0 & -y \\ -M & p\end{pmatrix}$. Fix a ring embedding $\iota$ of $\overline{\mathbb Q}$ into $\mathbb C$ and write $\overline{\mathbb Q}\cdot F(N)$ for [`ModularCurve.x1FunctionFieldBar N`](def/ModularCurve_X1.html#L182), the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of the $q$-expansion function field of level $N$. Let $\tau$ be a $\overline{\mathbb Q}$-algebra automorphism of $\overline{\mathbb Q}\cdot F(Mp)$ subject to the hypothesis: for every element $x$, every weight $k$, all modular forms $f, g, \varphi, \psi$ of weight $k$ on $\Gamma_1(Mp)$ and nonzero integers $D, E$ with $\varphi = D\,(f\mid_k\gamma)(\mathrm{diag}(p,1)\,\cdot)$ and $\psi = E\,(g\mid_k\gamma)(\mathrm{diag}(p,1)\,\cdot)$ as functions on $\mathcal H$, with the $q$-expansion of $g$ nonzero, if $\iota$ applied coefficientwise to $x$ is $\hat f/\hat g$, then $\iota$ applied coefficientwise to $\tau x$ is $(E/D)\,\hat\varphi/\hat\psi$. Let $\alpha_1, \beta_1 : \overline{\mathbb Q}\cdot F(M) \to \overline{\mathbb Q}\cdot F(Mp)$ be $\overline{\mathbb Q}$-algebra homomorphisms such that $\alpha_1$ is the identity on underlying Laurent series and $\beta_1$ is the substitution $q \mapsto q^p$ (scaling of exponents by $p$). Assume further that [`ModularCurve.diamondAut M p`](def/ModularCurve_X1Diamond.html#L66) satisfies the defining property of a diamond automorphism at $p$ on the level-$M$ function field — $\gcd(p,M)=1$, and for all weight-$k$ forms $f, g$ on $\Gamma_1(M)$ with integral $q$-expansions $p_f, p_g$, $p_g$ giving a nonzero series, and all $\delta \in \Gamma_0(M)$ with $\delta_{00} \equiv p \pmod M$, the image of $p_f/p_g$ under the automorphism, times the $q$-expansion of $g\mid_k\delta$, equals that of $f\mid_k\delta$ — and that [`ModularCurve.diamondAutBar M p`](def/ModularCurve_X1Diamond.html#L94) is its base change to $\overline{\mathbb Q}$, i.e. agrees with it on coefficientwise images of level-$M$ elements. Then $\tau \circ \alpha_1 = \beta_1$ and $\tau \circ \beta_1 = \alpha_1 \circ \langle p\rangle$, where $\langle p\rangle$ denotes [`ModularCurve.diamondAutBar M p`](def/ModularCurve_X1Diamond.html#L94).
--
--   This is the function-field form of the classical statement that pull-back along the Atkin–Lehner matrix $W_p = \gamma\,\mathrm{diag}(p,1)$ at level $Mp$ (for $p \nmid M$) interchanges the two degeneracy embeddings of the level-$M$ function field, up to the diamond automorphism $\langle p \rangle$. It is used in the comparison of the diamond operator with the transported level-substitution and level-inclusion maps on the Jacobian side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_AtkinLehnerPartial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.XOneP.comp_alpha_eq_beta_and_comp_beta_eq_alpha_comp_diamondAutBar_of_atkinLehnerSlash_p
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)

    (y w₀ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1)
    (γ γ' : SL(2, ℤ)) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y; (M : ℤ), (p : ℤ) * w₀])
    (hγ' : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![w₀, -y; -(M : ℤ), (p : ℤ)])
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (τ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hτ :

      (∀ (x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (k : ℤ) (f g φ ψ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((τ x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)))

    (α₁ β₁ : ↥(ModularCurve.x1FunctionFieldBar M) →ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hα : ∀ u : ↥(ModularCurve.x1FunctionFieldBar M), ((α₁ u : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u : ↥(ModularCurve.x1FunctionFieldBar M), ((β₁ u : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hdia : ModularCurve.IsDiamondAut M p (ModularCurve.diamondAut M p))
    (hbc : ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ) (ModularCurve.diamondAut M p) (ModularCurve.diamondAutBar M p)) :
    τ.toAlgHom.comp α₁ = β₁ ∧
    τ.toAlgHom.comp β₁ = α₁.comp (ModularCurve.diamondAutBar M p).toAlgHom := by sorry
