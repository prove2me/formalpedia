-- Prove2me | Theorems.Thm_ModularCurve_XOneP_coe_apply_eq_coeffEmb_qExpand_mul_jq_of_atkinLehnerSlash_p
-- name    : ModularCurve.XOneP.coe_apply_eq_coeffEmb_qExpand_mul_jq_of_atkinLehnerSlash_p
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/1415c66f-7d8d-5870-be3c-ef9ace99e43d
-- title:
--   Slash transport along Wₚ swaps j(q^e) and j(q^{ep})
-- statement:
--   Fix a prime $p$, a nonzero natural number $M$ with $p \nmid M$, integers $y, w_0$ with $p w_0 - M y = 1$, and $\gamma \in \mathrm{SL}(2,\mathbb{Z})$ whose matrix is $\begin{pmatrix} 1 & y \\ M & p w_0\end{pmatrix}$; fix a ring embedding $\iota : \overline{\mathbb{Q}} \to \mathbb{C}$ and a $\overline{\mathbb{Q}}$-algebra automorphism $\tau$ of [`ModularCurve.x1FunctionFieldBar (M * p)`](def/ModularCurve_X1.html#L182), the intermediate field of $\overline{\mathbb{Q}} \subseteq \mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) of the rational function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137). Two hypotheses on $\tau$ are assumed. First, a transport law: whenever $x$ lies in that field, $f, g, \varphi, \psi$ are weight-$k$ modular forms on $\Gamma_1(Mp)$ and $D, E$ are nonzero integers with $\varphi(z) = D\,(f\mid_k\gamma)(\mathrm{diag}(p,1)\cdot z)$ and $\psi(z) = E\,(g\mid_k\gamma)(\mathrm{diag}(p,1)\cdot z)$ on $\mathbb{H}$, the level-one $q$-expansion of $g$ is nonzero, and the coefficientwise image under $\iota$ of the Laurent series $x$ is the ratio of the $q$-expansions of $f$ and $g$, then the image of $\tau x$ under $\iota$ equals $(E/D)$ times the ratio of the $q$-expansions of $\varphi$ and $\psi$. Second, $\tau$ sends any element whose Laurent series is [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) (that is, $q^{-1}$ times the power series `jNumQ`) to the element with Laurent series $j(q^p)$, the image of `jq` under the exponent-scaling homomorphism [`ModularCurve.qExpand ℚ p`](def/ModularCurve_X0.html#L25). The conclusion: for every nonzero $e \mid M$, $\tau$ sends any element with Laurent series $j(q^e)$ to the one with Laurent series $j(q^{ep})$, and any element with Laurent series $j(q^{ep})$ to the one with Laurent series $j(q^{e})$, all read through `coeffEmb`.
--
--   This records the action of the Atkin–Lehner transport at $p$ on the degenerate modular functions $j(q^e)$, $e \mid M$, inside the function field of $X_1(Mp)$ base changed to $\overline{\mathbb{Q}}$: the involution interchanges the $e$- and $ep$-scaled $j$-expansions. It feeds the construction of the automorphism of that function field used to compare the Hecke and diamond operators at $p$ under the full Atkin–Lehner involution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_coe_apply_eq_coeffEmb_qExpand_mul_jq_of_atkinLehnerSlash_p.lean

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

theorem ModularCurve.XOneP.coe_apply_eq_coeffEmb_qExpand_mul_jq_of_atkinLehnerSlash_p
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (y w₀ : ℤ) (hrel : (p : ℤ) * w₀ - (M : ℤ) * y = 1)
    (γ : SL(2, ℤ)) (hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y; (M : ℤ), (p : ℤ) * w₀])
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (τ : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hE1 :
      (∀ (x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (k : ℤ) (f g φ ψ : ModularForm (CongruenceSubgroup.Gamma1 (M * p) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] γ) (ModularForm.heckeDiagMatrix p • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((τ x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)))
    (hE2 :
      (∀ j : ↥(ModularCurve.x1FunctionFieldBar (M * p)), ((j : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq →
        ((τ j : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ p ModularCurve.jq))) :
    (∀ (e : ℕ) [NeZero e], e ∣ M →
      (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)), ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ e ModularCurve.jq) →
        ((τ x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ (e * p) ModularCurve.jq)) ∧
      (∀ x : ↥(ModularCurve.x1FunctionFieldBar (M * p)), ((x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ (e * p) ModularCurve.jq) →
        ((τ x : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ e ModularCurve.jq))) := by sorry
