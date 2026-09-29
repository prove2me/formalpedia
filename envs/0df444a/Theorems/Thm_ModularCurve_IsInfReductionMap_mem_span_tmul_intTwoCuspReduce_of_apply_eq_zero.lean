-- Prove2me | Theorems.Thm_ModularCurve_IsInfReductionMap_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero
-- name    : ModularCurve.IsInfReductionMap.mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/ee8cc3a8-1838-5b70-81c6-03cfdbc1b1a3
-- title:
--   Kernel of an ∞-reduction map is spanned by p-divisible classes
-- statement:
--   Let $p$ be a prime, let $M$ be a nonzero natural number with $p \mid M$, let $H \le (\mathbb{Z}/M)^{\times}$, and let $W$ be an Atkin–Lehner datum for $(M,p)$, i.e. data $R$, $a$, $b$ with $M = pR$ and $pa - Rb = 1$ (the variable $W$ occurs in no other binder of the statement). Let $K$ be a field equipped with a $\mathbb{Z}/p$-algebra structure. Write $L =$ [`CuspForm.twoCuspLattice M H 2 p ⊥`](def/CuspForm_TwoCuspLattice.html#L86) for the $\mathbb{Z}$-submodule of weight-two cusp forms on $\Gamma_H(M)$ spanned by those $f$ all of whose $q$-coefficients, and all of whose $q$-coefficients after Atkin–Lehner slashing by an arbitrary datum at $(M,p)$, are rational integers after applying any element of the Hecke ring `heckeRingH M H 2`; let $\Omega_0 =$ [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) be the quotient of $L$ by `intIdeal p • ⊤`, with reduction map [`CuspForm.intTwoCuspReduce`](def/ModularCurve_XHDifferentialsModL.html#L401). Let $F =$ [`ModularCurve.qExpFunctionFieldC K`](def/ModularCurve_X1.html#L101) of $\Gamma_{H'}(M/p)$, where $H'$ is the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$, and let $\rho \colon K \otimes_{\mathbb{Z}/p} \Omega_0 \to \Omega[F/K]$ be a $K$-linear map satisfying `IsInfReductionMap`: for every $f$ in the two-cusp integral set and every $P \in \mathbb{Z}[[q]]$ whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of $f$, the $q$-expansion of the differential $\rho(1 \otimes \bar f)$ equals the coefficientwise image of $P$ in the Laurent series over $K$. Then every $x$ in the kernel of $\rho$ lies in the $K$-span of the elements $1 \otimes$ `intTwoCuspReduce` $y$ with $y \in L$ such that each $q$-coefficient of $y$ is $p$ times an integer.
--
--   This is the flat base change computation of the kernel of the $\infty$-component reduction map on weight-two cusp forms modulo $p$: over $\mathbb{F}_p$ the kernel of coefficientwise reduction consists of the classes of forms with all $q$-coefficients divisible by $p$, and the conclusion records that passing to $K$ introduces nothing further. It is used by [`ModularCurve.IsInfReductionMap.baseChange_genU_self_apply_eq_zero_of_apply_eq_zero`](thm.html#ModularCurve.IsInfReductionMap.baseChange_genU_self_apply_eq_zero_of_apply_eq_zero) and by [`ModularCurve.eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash`](thm.html#ModularCurve.eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash), in the comparison of differentials on the two degeneracy components of the modular curve at level divisible by $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsInfReductionMap_mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct ModularForm MatrixGroups

theorem ModularCurve.IsInfReductionMap.mem_span_tmul_intTwoCuspReduce_of_apply_eq_zero
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (W : ModularForm.AtkinLehnerDatum M p)
    (K : Type*) [Field K] [Algebra (ZMod p) K]
    {ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]}
    (hρ : ModularCurve.IsInfReductionMap K p M H hpM ρ)
    (x : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p) (hx : ρ x = 0) :
    x ∈ Submodule.span K {z : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p |
      ∃ y : ↥(CuspForm.twoCuspLattice M H 2 p (⊥ : Subring ℂ)),
        (∀ n : ℕ, ∃ m : ℤ, ModularFormClass.qCoeff (⇑(y : CuspForm (CohCarrier.GammaH M H) 2)) n = (p : ℂ) * m) ∧
        z = (1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p y} := by sorry
