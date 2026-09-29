-- Prove2me | Theorems.Thm_ModularCurve_XOneGammaZeroP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1x0_gamma0
-- name    : ModularCurve.XOneGammaZeroP.exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1x0_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/1b91c9da-d12d-5d3d-b4fa-4411f041d8cb
-- title:
--   Atkin–Lehner automorphism of the Γ₁(M)∩Γ₀(p) q-expansion field
-- statement:
--   Let $p$ be a prime, let $M$ be a positive integer with $p \nmid M$, and let $L$ be a field of characteristic zero which is a $p$-th cyclotomic extension of $\mathbb{Q}$. Let $K_1$ be an intermediate field of $L \subseteq L((q))$ (the Laurent series field `LaurentSeries L`) which is assumed equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p)`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of $L((q))$ generated over $L$ by the coefficientwise images under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) (the map induced by $\mathbb{Q} \to L$ on Laurent coefficients) of the elements of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the set [`ModularCurve.intFormRatiosC ℚ (Gamma1 M ⊓ Gamma0 p)`](def/ModularCurve_X1.html#L83). Let $j \in K_1$ be an element whose underlying Laurent series is the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the series $q^{-1}$ times the rational power series `jNumQ`. The assertion is that there exists an $L$-algebra automorphism $\sigma$ of $K_1$ with two properties. First, the Laurent series underlying $\sigma(j)$ is the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of [`ModularCurve.qExpand ℚ p ModularCurve.jq`](def/ModularCurve_X0.html#L25), the series obtained from $j(q)$ by multiplying all exponents by $p$, i.e. $j(q^p)$. Second, for every $f$ in [`ModularCurve.modularFunctionFieldFull (M * p)`](def/ModularCurve_X0.html#L305), the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the series $j(q^d)$ for the nonzero divisors $d$ of $Mp$, and every proof that the coefficientwise image of $f$ lies in $K_1$, the value of $\sigma$ at the corresponding element of $K_1$ has underlying Laurent series the coefficientwise image of [`ModularCurve.atkinLehnerInvolutionFull M p f`](def/ModularCurve_AtkinLehnerPartial.html#L21); here `atkinLehnerInvolutionFull M p` is a chosen $\mathbb{Q}$-algebra automorphism $w$ of `modularFunctionFieldFull (M * p)` satisfying `IsAtkinLehnerAutFull M p`, namely $w(j(q^d)) = j(q^{dp})$ and $w(j(q^{dp})) = j(q^d)$ for all nonzero $d \mid M$, with the identity taken if no such automorphism exists.
--
--   This realises the Atkin–Lehner involution $W_p$ at the prime $p$ as an automorphism of the $q$-expansion function field of $X(\Gamma_1(M) \cap \Gamma_0(p))$ base-changed to a $p$-th cyclotomic field, pinned down both by its effect $j(q) \mapsto j(q^p)$ and by its compatibility with the all-divisors involution of the level-$Mp$ field $\mathbb{Q}(j(q^e) : e \mid Mp)$. It is used in the construction of the pair of automorphisms in [`ModularCurve.XOneGammaZeroP.exists_algEquiv_pair_map_j_eq_qExpand_and_coe_comp_eq_x1x0_gamma0`](thm.html#ModularCurve.XOneGammaZeroP.exists_algEquiv_pair_map_j_eq_qExpand_and_coe_comp_eq_x1x0_gamma0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneGammaZeroP_exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1x0_gamma0.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_AtkinLehnerPartial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.XOneGammaZeroP.exists_algEquiv_map_j_eq_qExpand_and_coe_eq_atkinLehnerInvolutionFull_x1x0_gamma0
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    [NeZero p] :
    ∃ σ : ↥K₁ ≃ₐ[L] ↥K₁,
      ((σ j : ↥K₁) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq) ∧
      (∀ (f : ↥(ModularCurve.modularFunctionFieldFull (M * p)))
        (hfK : ModularCurve.coeffEmb L (f : LaurentSeries ℚ) ∈ K₁),
        ((σ ⟨ModularCurve.coeffEmb L (f : LaurentSeries ℚ), hfK⟩ : ↥K₁) : LaurentSeries L) =
          ModularCurve.coeffEmb L ((ModularCurve.atkinLehnerInvolutionFull M p f : ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ)) := by sorry
