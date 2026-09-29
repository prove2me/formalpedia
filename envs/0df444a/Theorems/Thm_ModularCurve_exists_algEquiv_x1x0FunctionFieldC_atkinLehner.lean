-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_x1x0FunctionFieldC_atkinLehner
-- name    : ModularCurve.exists_algEquiv_x1x0FunctionFieldC_atkinLehner
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/dfd9f457-825b-50a8-bc96-1dbf25df0f9d
-- title:
--   Atkin–Lehner automorphism interchanging the two degeneracy embeddings
-- statement:
--   Let $M\ge 1$, let $\ell$ be a prime with $\ell\nmid M$, and write $F_0=$ `x1FunctionField M` for the $q$-expansion function field of $X_1(M)$ inside $\mathbb{Q}((q))$ and $F_0'=$ `x1x0FunctionFieldC ℚ M (M*ℓ)` for that of $\Gamma_1(M)\cap\Gamma_0(M\ell)$; for a field $L\supseteq\mathbb{Q}$, `laurentBaseChange L` denotes the subfield of $L((q))$ generated over $L$ by the coefficientwise image of the given field. Assume: (i) `HeckeBetaOneDefined M ℓ`, i.e. the exponent-scaling ring map $q\mapsto q^{\ell}$ carries $F_0$ into $F_0'$; (ii) there exists a $\mathbb{Q}$-algebra automorphism $\sigma$ of $F_0$ with `IsDiamondAut M ℓ σ`, i.e. $\gcd(\ell,M)=1$ and for all $k$, all weight-$k$ modular forms $f,g$ on $\Gamma_1(M)$ with integral $q$-expansions $p_f,p_g$, $p_g\ne 0$ as a Laurent series, and all $\gamma\in\Gamma_0(M)$ with $\gamma_{00}\equiv\ell \pmod M$, the complex coefficientwise image of $\sigma(p_f/p_g)$ times `slashQExpC k g γ` equals `slashQExpC k f γ`; (iii) the automorphism `diamondAut M ℓ` of $F_0$ admits a base change to an $\overline{\mathbb{Q}}$-automorphism of `laurentBaseChange (AlgebraicClosure ℚ) F₀`, in the sense of `IsBaseChangeAutOf`. Then there is an $\overline{\mathbb{Q}}$-algebra automorphism $W$ of `laurentBaseChange (AlgebraicClosure ℚ) F₀'` such that for every $x$ in `x1FunctionFieldBar M` one has $W(\beta(x))=\alpha(x)$ and $W(\alpha(x))=\beta\big(\langle\ell\rangle^{-1}x\big)$, where $\alpha=$ `heckeAlphaOneBar` is the inclusion, $\beta=$ `heckeBetaOneBar` is the map induced by $q\mapsto q^{\ell}$, and $\langle\ell\rangle=$ `diamondAutBar M ℓ`.
--
--   This is the Atkin–Lehner automorphism $W_\ell$ of $X(\Gamma_1(M)\cap\Gamma_0(M\ell))$ in its function-field form: it swaps the two degeneracy embeddings of the function field of $X_1(M)$, up to the diamond operator $\langle\ell\rangle$. It is used in the comparison of $q$-expansion coefficients along the two degeneracy maps, namely by [`ModularCurve.coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd`](thm.html#ModularCurve.coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_x1x0FunctionFieldC_atkinLehner.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_X1Diamond

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_algEquiv_x1x0FunctionFieldC_atkinLehner
    (M : ℕ) [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (hβ : ModularCurve.HeckeBetaOneDefined M ℓ)
    (hσ : ∃ σ : ↥(ModularCurve.x1FunctionField M) ≃ₐ[ℚ] ↥(ModularCurve.x1FunctionField M),
      ModularCurve.IsDiamondAut M ℓ σ)
    (hσ' : ∃ σ' : ↥(ModularCurve.x1FunctionFieldBar M) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.x1FunctionFieldBar M),
      ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ) (ModularCurve.diamondAut M ℓ) σ') :
    ∃ W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ))) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ))),
      (∀ x : ↥(ModularCurve.x1FunctionFieldBar M),
        W (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ x) =
          ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ x) ∧
      ∀ x : ↥(ModularCurve.x1FunctionFieldBar M),
        W (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ x) =
          ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ
            ((ModularCurve.diamondAutBar M ℓ).symm x) := by sorry
