-- Prove2me | Theorems.Thm_ModularCurve_span_ssPolarDifferentials_atkinLehnerPinned_eq_top
-- name    : ModularCurve.span_ssPolarDifferentials_atkinLehnerPinned_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/a7b84e4d-23c1-54bd-980a-d3062985a937
-- title:
--   Atkin–Lehner-pinned differentials span the supersingular-polar space
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb Z/M)^\times$ containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is $1$; assume $M/p \neq 0$. Let $K$ be an algebraically closed field of characteristic $p$, viewed as a $\mathbb Z/p$-algebra. Let $\rho^{\infty}$ be a $K$-linear map from $K \otimes_{\mathbb Z/p} \mathrm{IntTwoCuspForms}\,M\,H\,p$ (that is, `TwoCuspForms M H 2 p ⊥ (intIdeal p)`, the weight-$2$ two-cusp module over the prime subring of $\mathbb C$ reduced modulo `intIdeal p`) to the module of Kähler differentials $\Omega$ of the $q$-expansion function field `qExpFunctionFieldC` over $K$ for the group $\Gamma_{H'}(M/p)$, where $H'$ is the image of $H$ in $(\mathbb Z/(M/p))^\times$. Assume $\rho^{\infty}$ satisfies `IsInfReductionMap`: for every $f$ in the two-cusp integral set `twoCuspIntegralSet M H 2 p ⊥` (all $q$-coefficients of $tf$ and of $(tf)$ slashed by any Atkin–Lehner datum at $(M,p)$ lie in that subring, for all $t$ in the Hecke ring) and every $pf \in \mathbb Z[[q]]$ with `IsIntegralQExp f pf`, the $q$-expansion of $\rho^{\infty}(1 \otimes \bar f)$ is `intSeriesC K pf`; and assume the range of $\rho^{\infty}$ is the space of supersingular-polar differentials, i.e. those $\omega \in \Omega$ regular outside the set `ssPlacesQExp` of places and with at most a simple pole at each of them. Let $W_d$ be an Atkin–Lehner datum for $(M, M/p)$, consisting of $R$ with $M = (M/p)R$ and $a, b \in \mathbb Z$ with $(M/p)a - Rb = 1$, and let $e \in (\mathbb Z/M)^\times$ have image $\bar e$ with $\bar e \cdot \bar p = 1$ in $\mathbb Z/(M/p)$. Then the $K$-span, inside the space of supersingular-polar differentials, of those $\omega$ for which there exist $f \in$ `twoCuspIntegralSet M H 2 p ⊥` of weight $2$ for $\Gamma_H(M)$, a natural number $D$ with $p \nmid D$ and a power series $pfW$ over the integral closure of $\mathbb Z$ in $\mathbb C$ whose image in $\mathbb C[[q]]$ is the width-$1$ $q$-expansion of $D \cdot \bigl(\langle e \rangle f\bigr)\big|_2 W_d$ (the diamond operator `diamondLinH` followed by `alSlash`), and such that $\omega = \rho^{\infty}(1 \otimes \overline{f})$, is the whole space.
--
--   The statement asserts that the supersingular-polar differentials at level $\Gamma_{H'}(M/p)$ over $K$ are already spanned by the images under a reduction map of those two-cusp integral weight-$2$ forms whose twist by the diamond operator $\langle e \rangle$ and by the Atkin–Lehner datum $W_d$ acquires algebraic-integer $q$-coefficients after a prime-to-$p$ rescaling; spanning holds because, by [`CuspForm.exists_not_dvd_and_algInt_qExpansion_smul_alSlash_diamond_of_mem_twoCuspIntegralSet_of_ker_le`](thm.html#CuspForm.exists_not_dvd_and_algInt_qExpansion_smul_alSlash_diamond_of_mem_twoCuspIntegralSet_of_ker_le), this pinning condition is satisfied by every two-cusp integral form. It is used in the construction of the Atkin–Lehner twisting isomorphism between supersingular-polar differentials and the mod $p$ cusp-form module compatible with transposed Hecke operators, in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_span_ssPolarDifferentials_atkinLehnerPinned_eq_top.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

theorem ModularCurve.span_ssPolarDifferentials_atkinLehnerPinned_eq_top
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra (ZMod p) K]

    (ρinf : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K])
    (hρinf : ModularCurve.IsInfReductionMap K p M H hpM ρinf)
    (hrange : LinearMap.range ρinf = ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)

    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    :
    Submodule.span K {ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) |
        ∃ (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
          (D : ℕ) (_ : ¬ p ∣ D) (pfW : PowerSeries ↥(integralClosure ℤ ℂ)),
          pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
            UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f)) ∧
          ((ω : ↥(ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p)) : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
            ρinf ((1 : K) ⊗ₜ[ZMod p] CuspForm.intTwoCuspReduce M H p
              ⟨f, CuspForm.twoCuspIntegralSet_subset_twoCuspLattice M H 2 p ⊥ hf⟩)} = ⊤ := by sorry
