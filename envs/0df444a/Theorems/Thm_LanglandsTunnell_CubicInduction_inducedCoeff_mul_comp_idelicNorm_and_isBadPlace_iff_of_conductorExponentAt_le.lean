-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le
-- name    : LanglandsTunnell.CubicInduction.inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/eb4b6eb4-8b73-5134-b374-6569592f5ba6
-- title:
--   Twisting a cubic idelic character by χ ∘ N
-- statement:
--   Let $K$ be a number field of degree $3$ over $\mathbb{Q}$, equipped with an integral $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$. Let $\mu$ be a character of the ideles of $K$ and $\chi$ one of the ideles of $\mathbb{Q}$, both admissible twists in the sense of being trivial on the principal ideles, continuous, and of absolute value $1$ at every idele. Assume: at every finite place $v$ of $\mathbb{Q}$ which is not a bad place for $(K,\mu)$ — i.e. neither some prime of $K$ above $v$ has $\mathrm{ramificationIdx}' \ne 1$, nor the predicate `IsTwistRamifiedAbove` holds for $\mu$ at $v$ — the local character $\chi_v$ is trivial on the units of the valuation ring; and there is $c : \{\text{finite places of }\mathbb{Q}\} \to \mathbb{N}$ such that at every bad $v$ the character $\chi_v$ has conductor exponent exactly $c(v)$ (trivial on the $c(v)$-th higher unit group, nontrivial on each lower one) while $\mathrm{conductorExponentAt}(\mu_w) + 12 \le c(v)$ for every prime $w$ of $K$ above $v$. Put $\mu' = \mu \cdot (\chi \circ N)$, $N$ the idelic norm of $K/\mathbb{Q}$ attached to `genuineBaseChange`. Then: $\mu'$ is an admissible twist; for $v$ not bad and $w \mid v$, $\mathrm{inducedCoeff}(\mu')_w = \chi(\varpi_v)^{f(v,w)} \cdot \mathrm{inducedCoeff}(\mu)_w$, where $\mathrm{inducedCoeff}$ is the value at the uniformizer idele when the character is unramified there and $0$ otherwise, $\varpi_v$ the uniformizer idele at $v$ and $f(v,w) = \mathrm{inertiaDeg}'$; the bad places of $\mu'$ are exactly those of $\mu$; above every bad $v$, $\mu'$ is ramified at each $w \mid v$; and for bad $v$, $3c(v) \le 12 + \sum_{w \mid v} f(v,w)\,\mathrm{pinnedExp}(\mu')_w$, the pinned exponent being the conductor exponent of $\mu'_w$ plus the level of the standard local additive character at $w$.
--
--   This is the bookkeeping step controlling how the local invariants of a cubic idelic character behave under twisting by a character of the base composed with the idelic norm: admissibility, unramified Hecke coefficients, the set of bad places, forced ramification above bad places, and a lower bound on the conductor of the twist in terms of pinned exponents. It is used in the construction of the cubic induction datum at bad places, [`LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad`](thm.html#LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

theorem LanglandsTunnell.CubicInduction.inducedCoeff_mul_comp_idelicNorm_and_isBadPlace_iff_of_conductorExponentAt_le
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχ : IsAdmissibleTwist ℚ χ)
    (hoff : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v → IsUnramifiedCharAt χ v)
    (c : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hc : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
      LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar χ v) (c v) ∧
        ∀ w ∈ primeFibre ℚ K v,
          LanglandsTunnell.TateLocal.conductorExponentAt K w (localChar μ w) + 12 ≤ c v) :
    IsAdmissibleTwist K (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ v → ∀ w ∈ primeFibre ℚ K v,
      inducedCoeff K (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w =
        (χ (uniformizerIdele ℚ v) : ℂ) ^ (v.asIdeal.inertiaDeg' w.asIdeal) *
          inducedCoeff K μ w) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ),
      IsBadPlace K (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) v ↔ IsBadPlace K μ v) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
      (∀ w ∈ primeFibre ℚ K v, ¬ IsUnramifiedCharAt
        (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w)) ∧
    (∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
      3 * (c v : ℤ) ≤ 12 +
        ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K
          (μ * χ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) w) := by sorry
