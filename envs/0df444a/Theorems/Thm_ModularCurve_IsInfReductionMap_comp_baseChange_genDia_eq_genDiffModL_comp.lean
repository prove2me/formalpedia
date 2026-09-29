-- Prove2me | Theorems.Thm_ModularCurve_IsInfReductionMap_comp_baseChange_genDia_eq_genDiffModL_comp
-- name    : ModularCurve.IsInfReductionMap.comp_baseChange_genDia_eq_genDiffModL_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/0df9076a-44e1-5b6a-a4e1-265f8941a55e
-- title:
--   Reduction to the infinity component intertwines ⟨ d⟩
-- statement:
--   Let $p$ be a prime, $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, and $H \le (\mathbb{Z}/M)^{\times}$ a subgroup containing every unit whose image under the reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ is trivial. Let $K$ be an algebraically closed field equipped with a $\mathbb{Z}/p$-algebra structure, $S$ a set of naturals, and write $\Gamma' = \mathrm{GammaH}(M/p, H')$ for the congruence subgroup attached to the image $H'$ of $H$ in $(\mathbb{Z}/(M/p))^{\times}$, and $\bar F =$ `qExpFunctionFieldC K` $\Gamma'$ for the subfield of $K((q))$ generated over $K$ by the reduced integral $q$-expansion ratios for $\Gamma'$. Let $\rho$ be a $K$-linear map from $K \otimes_{\mathbb{Z}/p} \mathrm{IntTwoCuspForms}(M,H,p)$, the mod-$p$ quotient of the two-cusp integral lattice of weight-two cusp forms on $\mathrm{GammaH}(M,H)$, to the Kähler differentials $\Omega[\bar F / K]$, and assume `IsInfReductionMap`: for every weight-two cusp form $f$ on $\mathrm{GammaH}(M,H)$ lying in the two-cusp integral set at $p$ over the subring $\bot \subseteq \mathbb{C}$ and every integral power series $pf$ whose image in $\mathbb{C}[[q]]$ is the $q$-expansion of $f$, the $q$-expansion `diffQExp` of $\rho(1 \otimes \bar f)$ is the coefficientwise image of $pf$ in the Laurent series over $K$. Then for every $d \in (\mathbb{Z}/M)^{\times}$, the composite of the $K$-base change of the mod-$p$ operator `intTwoCuspGenMod` attached to the generator $\mathrm{dia}\,d$ followed by $\rho$ equals the composite of $\rho$ followed by `genDiffModL` at $\mathrm{dia}\,d$, namely the diamond operator `diamondDiffModLH` on $\Omega[\bar F / K]$ for the image of $d$ in $(\mathbb{Z}/(M/p))^{\times}$.
--
--   This is the diamond-operator case of the compatibility between the mod-$p$ Hecke action on two-cusp integral weight-two forms of level $\Gamma_H(M)$ and the action on differentials of the component through the cusp $\infty$ of the Deligne–Rapoport reduction, identified with $X_{H'}(M/p)$ in characteristic $p$. It is used, together with its $T_\ell$ and $U_q$ analogues, in the comparison of Hecke modules underlying the level-lowering step, and is cited by results on $q$-coefficients of $\langle d\rangle f$ and on Atkin–Lehner pinning.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsInfReductionMap_comp_baseChange_genDia_eq_genDiffModL_comp.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.IsInfReductionMap.comp_baseChange_genDia_eq_genDiffModL_comp
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K] (S : Set ℕ)
    {ρ : K ⊗[ZMod p] CuspForm.IntTwoCuspForms M H p →ₗ[K]
        Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]}
    (hρ : ModularCurve.IsInfReductionMap K p M H hpM ρ)
    (d : (ZMod M)ˣ) :
    ρ ∘ₗ (CuspForm.intTwoCuspGenMod M H p S (CohCarrier.Gen.dia d)).baseChange K =
      ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia d) ∘ₗ ρ := by sorry
