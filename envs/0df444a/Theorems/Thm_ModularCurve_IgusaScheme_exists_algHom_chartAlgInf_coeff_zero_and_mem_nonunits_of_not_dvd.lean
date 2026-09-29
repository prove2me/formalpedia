-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd
-- name    : ModularCurve.IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/9d7bfcde-8b0c-5311-87b6-93098e52b4f8
-- title:
--   Cuspidal sections and cusp coordinate j(qᵖ)/jᵖ for X₀(Np)
-- statement:
--   Let $N \ge 1$ and let $p$ be a prime with $p \nmid N$. Write $F = \mathbb{Q}(\text{divisorExpansions}(Np)) \subseteq \mathbb{Q}((q))$ for `modularFunctionFieldFull (N * p)`, $\mathbb{Z}_{(p)}$ for [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of rationals whose denominator is coprime to $p$, and $w$ for `atkinLehnerInvolutionFull N p`, the chosen $\mathbb{Q}$-algebra automorphism of $F$ interchanging $j(q^{d})$ and $j(q^{dp})$ for every nonzero $d \mid N$ (the identity if none exists). Set $u = j^{-1}$, $jp = j(q^{p}) =$ `qExpand ℚ p jq`, and $t = jp \cdot u^{p}$, and let $B =$ `chartAlgInf (N * p) p` be the subalgebra of elements of $F$ integral over $\mathbb{Z}_{(p)}[u]$. Three assertions are made. First, there is a family $\varepsilon : \mathrm{Fin}\,2 \to (B \to_{\mathbb{Z}_{(p)}} \mathbb{Z}_{(p)})$ of $\mathbb{Z}_{(p)}$-algebra homomorphisms such that for all $b \in B$, $\varepsilon_0(b)$ is the coefficient of $q^{0}$ in $b$ and $\varepsilon_1(b)$ is the coefficient of $q^{0}$ in $w(b)$. Second, $t \in B$; there is a monic $h \in \mathbb{Z}[X][T]$ with $h$ mapped under $X \mapsto 0$ to $T^{p+1} - T^{p}$ and with $h(u,t) = 0$ in $F$; moreover the $q^{0}$-coefficient of $t$ is $1$ and that of $w(t)$ is $0$. Third, for any valuation subrings $W_0, W_1$ of $F$ such that $f \in W_0$ exactly when there are Laurent series $x, y$ over $\mathbb{Z}$ with $y$ nonzero modulo $p$ and $f \cdot y = x$ after coefficientwise base change to $\mathbb{Q}$, and such that $f \in W_1$ exactly when $w(f) \in W_0$, one has $t - 1 \in W_0.\mathrm{nonunits}$ with the $q^{0}$-coefficient of $w(t-1)$ equal to $-1$, and $t^{p} - u^{p^{2}-1} \in W_1.\mathrm{nonunits}$ with the $q^{0}$-coefficient of $t^{p} - u^{p^{2}-1}$ equal to $1$.
--
--   This is the cuspidal part of the Deligne–Rapoport description of $X_0(Np)$ over $\mathbb{Z}_{(p)}$ for $p \nmid N$: the cusps $\infty$ and $0 = w(\infty)$ give two sections of the pole chart, the function $t = j(q^{p})/j^{p}$ is an integral coordinate separating their reductions modulo $p$, and the two cusps lie in the nonunit loci of the two Gauss valuation rings, i.e. on the two distinct irreducible components of the special fibre. It is used downstream in the treatment of the cusps on the smooth locus of the model and of the induced maps on the fibres of the Igusa-type model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_AtkinLehnerPartial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_algHom_chartAlgInf_coeff_zero_and_mem_nonunits_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    let u : ↥(modularFunctionFieldFull (N * p)) := (jFull (N * p))⁻¹
    let jp : ↥(modularFunctionFieldFull (N * p)) :=
      ⟨qExpand ℚ p jq, jqd_mem_full (N * p) (dvd_mul_left p N)⟩
    let t : ↥(modularFunctionFieldFull (N * p)) := jp * u ^ p

    (∃ ε : Fin 2 → (↥(chartAlgInf (N * p) p) →ₐ[↥(GaloisRep.ratLocalizedAt p)]
        ↥(GaloisRep.ratLocalizedAt p)),
      ∀ b : ↥(chartAlgInf (N * p) p),
        ((ε 0 b : ↥(GaloisRep.ratLocalizedAt p)) : ℚ)
            = ((b : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ).coeff 0 ∧
        ((ε 1 b : ↥(GaloisRep.ratLocalizedAt p)) : ℚ)
            = ((atkinLehnerInvolutionFull N p (b : ↥(modularFunctionFieldFull (N * p))) :
                ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ).coeff 0) ∧

    (t ∈ chartAlgInf (N * p) p ∧
      (∃ h : Polynomial (Polynomial ℤ), h.Monic ∧
        h.map (Polynomial.evalRingHom 0) = X ^ (p + 1) - X ^ p ∧
        h.eval₂ (Polynomial.eval₂RingHom (algebraMap ℤ ↥(modularFunctionFieldFull (N * p))) u) t
          = 0) ∧
      ((t : ↥(modularFunctionFieldFull (N * p))) : LaurentSeries ℚ).coeff 0 = 1 ∧
      ((atkinLehnerInvolutionFull N p t : ↥(modularFunctionFieldFull (N * p))) :
        LaurentSeries ℚ).coeff 0 = 0) ∧

    (∀ W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull (N * p)),
      (∀ f : ↥(modularFunctionFieldFull (N * p)), f ∈ W₀ ↔
        ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
          (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y
            = coeffMap (Int.castRingHom ℚ) x) →
      (∀ f : ↥(modularFunctionFieldFull (N * p)), f ∈ W₁ ↔
        atkinLehnerInvolutionFull N p f ∈ W₀) →
      (t - 1 ∈ W₀.nonunits ∧
        ((atkinLehnerInvolutionFull N p (t - 1) : ↥(modularFunctionFieldFull (N * p))) :
          LaurentSeries ℚ).coeff 0 = -1) ∧
      (t ^ p - u ^ (p ^ 2 - 1) ∈ W₁.nonunits ∧
        ((t ^ p - u ^ (p ^ 2 - 1) : ↥(modularFunctionFieldFull (N * p))) :
          LaurentSeries ℚ).coeff 0 = 1)) := by sorry
