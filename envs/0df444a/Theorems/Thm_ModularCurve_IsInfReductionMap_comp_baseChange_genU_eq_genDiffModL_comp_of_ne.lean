-- Prove2me | Theorems.Thm_ModularCurve_IsInfReductionMap_comp_baseChange_genU_eq_genDiffModL_comp_of_ne
-- name    : ModularCurve.IsInfReductionMap.comp_baseChange_genU_eq_genDiffModL_comp_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/914497ae-5b2d-515a-8adc-56b8d855383a
-- title:
--   Reduction at infinity intertwines U_q for q ≠ p
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and let $H \le (\mathbb{Z}/M)^{\times}$ be a subgroup containing every unit that becomes $1$ under the reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$. Let $K$ be an algebraically closed field that is an algebra over $\mathbb{Z}/p$, and $S$ a set of natural numbers. Write $\Gamma' =$ [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) of level $M/p$ and of the subgroup `infSubgroup p M H hpM`, the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$, and let $F =$ `qExpFunctionFieldC K` $\Gamma'$, the intermediate field of $K((q))$ generated over $K$ by the reduced ratios of integral $q$-expansions for $\Gamma'$. Let $\rho$ be a $K$-linear map from $K \otimes_{\mathbb{Z}/p}$ [`CuspForm.IntTwoCuspForms M H p`](def/ModularCurve_XHDifferentialsModL.html#L374) — the quotient of the two-cusp lattice `twoCuspLattice M H 2 p` $\mathbb{Z}$ by `intIdeal p` — to $\Omega[F/K]$, and assume `IsInfReductionMap`: for every weight-two cusp form $f$ on [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) lying in `twoCuspIntegralSet M H 2 p` $\mathbb{Z}$ (all Hecke translates of $f$, before and after weight-two slashing by every Atkin–Lehner datum at $p$, have rational integral $q$-coefficients) and every integral power series $pf$ with $pf$ mapping to the $q$-expansion of $f$, the $q$-expansion `diffQExp` of $\rho(1 \otimes \overline{f})$ is the coefficientwise reduction `intSeriesC K` $pf$. Let $q$ be a prime with $q \mid M$ and $q \neq p$. Then $\rho$ composed after the $K$-base change of `intTwoCuspGenMod M H p S` applied to the generator `CohCarrier.Gen.U q` equals `genDiffModL K p M H hpM S` at that generator — which, since $q \neq p$, is `heckeDiffModLH K (M/p)` `(infSubgroup p M H hpM) q` — composed after $\rho$.
--
--   This is the compatibility of the mod $p$ reduction map onto the component through the cusp $\infty$ of the semistable model at $p$ with the operator $U_q$ at a prime $q \mid M$ different from $p$: on the two-cusp integral forms of level $\Gamma_H(M)$ the operator $U_q$ corresponds to the $U_q$ correspondence on differentials of $X_{H'}(M/p)$ over $K$. It is used in the identification of the reduction's image with the dual of the multiplicative part of the Tate module in the ordinary case, and in the Atkin–Lehner twist comparison for $U_q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsInfReductionMap_comp_baseChange_genU_eq_genDiffModL_comp_of_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.IsInfReductionMap.comp_baseChange_genU_eq_genDiffModL_comp_of_ne
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K] (S : Set ℕ)
    {ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]}
    (hρ : ModularCurve.IsInfReductionMap K p M H hpM ρ)
    (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqp : q ≠ p) :
    ρ ∘ₗ (CuspForm.intTwoCuspGenMod M H p S (CohCarrier.Gen.U q hq hqM)).baseChange K =
      ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U q hq hqM) ∘ₗ ρ := by sorry
