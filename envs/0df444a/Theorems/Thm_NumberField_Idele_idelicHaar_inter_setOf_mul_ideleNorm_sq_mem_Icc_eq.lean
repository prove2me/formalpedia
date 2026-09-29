-- Prove2me | Theorems.Thm_NumberField_Idele_idelicHaar_inter_setOf_mul_ideleNorm_sq_mem_Icc_eq
-- name    : NumberField.Idele.idelicHaar_inter_setOf_mul_ideleNorm_sq_mem_Icc_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/666f1731-974c-54cb-943e-cbdfc1f333d8
-- title:
--   Shift-invariance and finiteness of idelic norm shells
-- statement:
--   Let $L$ be a number field and let $\Omega_1$ be a subset of the idele group $(\mathbb{A}_L)^\times$, the unit group of the adele ring of $L$. Assume that $\Omega_1$ is a fundamental domain, for the Borel $\sigma$-algebra [`NumberField.Idele.ideleBorel L`](def/NumberField_IdeleProductMeasure.html#L384) on the idele group and the Haar measure [`NumberField.Idele.idelicHaar L`](def/NumberField_IdeleProductMeasure.html#L391) (namely `Measure.haar`), for the action of the range of the map induced on units by the structure homomorphism $L \to \mathbb{A}_L$, i.e. for the subgroup of principal ideles. Let $\alpha, \beta$ be reals with $0 < \alpha$ and $\alpha \le \beta$, and let $c$ be a real with $0 < c$. Here [`NumberField.TateGlobal.ideleNorm L u`](def/NumberField_TateGlobalZeta.html#L19) denotes the real number obtained from the value at $u$ of the distributive Haar character `distribHaarChar` of $\mathbb{A}_L$, i.e. the factor by which multiplication by $u$ scales the Haar measure of $\mathbb{A}_L$. The conclusion is twofold: first, the `idelicHaar L`-measure of $\Omega_1 \cap \{u : c\,\lvert u\rvert^2 \in [\alpha,\beta]\}$ equals that of $\Omega_1 \cap \{u : \lvert u\rvert^2 \in [\alpha,\beta]\}$, where $\lvert\cdot\rvert$ is this idelic norm; second, the latter measure is not $\infty$.
--
--   The sets cut out by bounds on the idelic norm are stable under the principal ideles by the product formula, so their volume inside a fundamental domain for $L^\times$ is a volume on the idele class group; the statement records that this shell volume is unchanged by a multiplicative shift of the norm bound and is finite, the finiteness reflecting compactness of the norm-one idele classes. It supplies the constant attached to the central variable of the Iwasawa decomposition in [`AutomorphicForm.exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2`](thm.html#AutomorphicForm.exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_idelicHaar_inter_setOf_mul_ideleNorm_sq_mem_Icc_eq.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem NumberField.Idele.idelicHaar_inter_setOf_mul_ideleNorm_sq_mem_Icc_eq
    (L : Type) [Field L] [NumberField L]
    (Ω₁ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ₁ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₁ (NumberField.Idele.idelicHaar L))
    (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (c : ℝ) (hc : 0 < c) :
    NumberField.Idele.idelicHaar L (Ω₁ ∩ {u | c * NumberField.TateGlobal.ideleNorm L u ^ 2 ∈ Set.Icc α β}) =
        NumberField.Idele.idelicHaar L (Ω₁ ∩ {u | NumberField.TateGlobal.ideleNorm L u ^ 2 ∈ Set.Icc α β}) ∧
      NumberField.Idele.idelicHaar L (Ω₁ ∩ {u | NumberField.TateGlobal.ideleNorm L u ^ 2 ∈ Set.Icc α β}) ≠ ⊤ := by sorry
