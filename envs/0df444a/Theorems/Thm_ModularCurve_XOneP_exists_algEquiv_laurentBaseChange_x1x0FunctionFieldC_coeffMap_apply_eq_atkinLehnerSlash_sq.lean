-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq
-- name    : ModularCurve.XOneP.exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/4d5ca534-9791-5754-82c9-42e97baaeb7a
-- title:
--   Atkin–Lehner automorphism W_{p²} of the Γ₁(Mp)∩Γ₀(Mp²) function field
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \nmid M$, let $y,w \in \mathbb{Z}$ satisfy $p^2 w - My = 1$, let $\delta,\delta' \in \mathrm{SL}_2(\mathbb{Z})$ have matrices $\begin{pmatrix}1&y\\ M&p^2w\end{pmatrix}$ and $\begin{pmatrix}w&-y\\ -M&p^2\end{pmatrix}$, and let $\iota \colon \overline{\mathbb{Q}} \to \mathbb{C}$ be a ring homomorphism from `AlgebraicClosure ℚ`. Write $\Gamma = \Gamma_1(Mp) \cap \Gamma_0(Mp^2)$, let $F_0 \subseteq \mathrm{LaurentSeries}\,\mathbb{Q}$ be the subfield generated over $\mathbb{Q}$ by the set `intFormRatiosC ℚ` $\Gamma$, and let $K \subseteq \mathrm{LaurentSeries}\,\overline{\mathbb{Q}}$ be the subfield generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of $F_0$ under $\mathbb{Q} \to \overline{\mathbb{Q}}$. The assertion is that there is an $\overline{\mathbb{Q}}$-algebra automorphism $W$ of $K$ with four properties, where throughout $\iota$ is applied coefficientwise to Laurent series, $q$-expansions are taken with width $1$ and viewed as Laurent series over $\mathbb{C}$, and `heckeDiagMatrix` $(p^2)$ is the element $\begin{pmatrix}p^2&0\\0&1\end{pmatrix}$ of $\mathrm{GL}_2(\mathbb{R})$, acting on the upper half-plane by $z \mapsto p^2 z$. First, every $x \in K$ admits a presentation: there are $k \in \mathbb{Z}$ and modular forms $f,g$ of weight $k$ on (the image in $\mathrm{GL}_2(\mathbb{R})$ of) $\Gamma$ with $q$-expansion of $g$ nonzero and $\iota_*(x) = f(q)/g(q)$, such that moreover each of the four functions $z \mapsto (f\mid_k \delta)(p^2 z)$, $z \mapsto (g\mid_k \delta)(p^2 z)$, $z \mapsto (f\mid_k \delta')(p^2 z)$, $z \mapsto (g\mid_k \delta')(p^2 z)$ becomes, after multiplication by a nonzero integer, a modular form of weight $k$ on $\Gamma$. Secondly, whenever $x$, $k$, $f$, $g$ are as above and $\varphi,\psi$ are weight-$k$ forms on $\Gamma$ with $\varphi = D \cdot (f\mid_k\delta)(p^2 \cdot)$ and $\psi = E \cdot (g\mid_k\delta)(p^2 \cdot)$ for nonzero integers $D,E$, then $\iota_*(W x) = (E/D)\,\varphi(q)/\psi(q)$. Thirdly, the same law with $\delta$ replaced by $\delta'$ computes $\iota_*(W^{-1} x)$. Fourthly, if the Laurent series underlying $j \in K$ is the image of `jq` $= q^{-1}\,$`jNumQ` under $\mathbb{Q} \to \overline{\mathbb{Q}}$, then the series underlying $W j$ is the image of `jq` after the substitution $q \mapsto q^{p^2}$ (multiplication of all exponents by $p^2$).
--
--   This realises the Atkin–Lehner operator at $p$ on the modular curve for $\Gamma_1(Mp) \cap \Gamma_0(Mp^2)$ — where the whole $p$-part $W_{p^2} = \delta\,\mathrm{diag}(p^2,1)$ occurs — as an automorphism of the $q$-expansion function field base-changed to $\overline{\mathbb{Q}}$, described by the slash transport law on presentations of elements as ratios of $q$-expansions of forms. Note that only the two transport laws, for $W$ and for $W^{-1}$ via $\delta'$, are asserted; the statement does not claim that $W$ is an involution. It feeds the comparison of the Atkin–Lehner conjugate of the Hecke and diamond automorphisms in [`ModularCurve.XOneP.exists_coprime_algEquiv_algEquiv_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_and_apply_heckeBetaOneBar_eq_of_atkinLehnerInvolutionFull`](thm.html#ModularCurve.XOneP.exists_coprime_algEquiv_algEquiv_apply_heckeAlphaOneBar_eq_heckeBetaOneBar_diamondAutBar_and_apply_heckeBetaOneBar_eq_of_atkinLehnerInvolutionFull).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq.lean

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

theorem ModularCurve.XOneP.exists_algEquiv_laurentBaseChange_x1x0FunctionFieldC_coeffMap_apply_eq_atkinLehnerSlash_sq
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)

    (y w : ℤ) (hrel : (p : ℤ) ^ 2 * w - (M : ℤ) * y = 1)
    (δ δ' : SL(2, ℤ)) (hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![1, y; (M : ℤ), (p : ℤ) ^ 2 * w])
    (hδ' : (δ' : Matrix (Fin 2) (Fin 2) ℤ) = !![w, -y; -(M : ℤ), (p : ℤ) ^ 2])
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    ∃ W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))) ≃ₐ[(AlgebraicClosure ℚ)] ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))),

      (∀ x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))), ∃ (k : ℤ) (f g : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k),
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 ∧
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ∧
        (∃ (φ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D : ℤ), D ≠ 0 ∧ (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (ψ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (E : ℤ), E ≠ 0 ∧ (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (φ' : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D' : ℤ), D' ≠ 0 ∧ (⇑φ' : UpperHalfPlane → ℂ) = (D' : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z))) ∧
        (∃ (ψ' : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (E' : ℤ), E' ≠ 0 ∧ (⇑ψ' : UpperHalfPlane → ℂ) = (E' : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z)))) ∧

      (∀ (x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) (k : ℤ) (f g φ ψ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ) (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((W x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)) ∧

      (∀ (x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) (k : ℤ) (f g φ ψ : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) ⊓ CongruenceSubgroup.Gamma0 (M * p * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (D E : ℤ),
        D ≠ 0 → E ≠ 0 →
        (⇑φ : UpperHalfPlane → ℂ) = (D : ℂ) • (fun z : UpperHalfPlane => ((⇑f) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        (⇑ψ : UpperHalfPlane → ℂ) = (E : ℂ) • (fun z : UpperHalfPlane => ((⇑g) ∣[k] δ') (ModularForm.heckeDiagMatrix (p ^ 2) • z)) →
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ≠ 0 →
        ModularCurve.coeffMap ι ((x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) →
        ModularCurve.coeffMap ι ((W.symm x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) =
          HahnSeries.C ((E : ℂ) / (D : ℂ)) * HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) / HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑ψ)) ∧

      (∀ j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p))), ((j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq →
        ((W j : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * p)))) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ (p ^ 2) ModularCurve.jq)) := by sorry
