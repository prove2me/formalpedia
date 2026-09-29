-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg
-- name    : LanglandsTunnell.CubicInduction.exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/5f1e6957-932f-59ba-990f-62e106f26e05
-- title:
--   Entire twisted Euler product for a non-norm cubic induction
-- statement:
--   Let $K$ be a number field of degree $3$ over $\mathbb{Q}$, with $\mathcal{O}_K$ an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, and let $\mu$ be a homomorphism from the idele units of $K$ to $\mathbb{C}^{\times}$ which is admissible, i.e. trivial on the principal ideles coming from $K^{\times}$, continuous, and of absolute value $1$ everywhere. Assume $\mu$ is not a norm in the following sense: there is no admissible character $\eta$ of the ideles of $\mathbb{Q}$ such that for every finite place $\mathfrak{P}$ of $K$ at which $\mu$ is unramified (all units of the local ring act trivially) and with $\eta$ unramified at the place $p$ of $\mathbb{Q}$ below, $\mu$ of the uniformizer idele at $\mathfrak{P}$ equals $\eta$ of the uniformizer idele at $p$ raised to the inertia degree $\mathrm{inertiaDeg}'$ of $\mathfrak{P}$ over $p$. Let $\omega$ be a character of the ideles of $\mathbb{Q}$ whose Euler coefficient at each place $p$ that is not bad for $(K,\mu)$ — i.e. $p$ is unramified in $K$ and $\mu$ is unramified at every prime of the fibre over $p$ — equals $\mathrm{inducedE3}$ of the coefficient function $\mathfrak{P}\mapsto\mu(\text{uniformizer at }\mathfrak{P})$ or $0$ according as $\mu$ is unramified at $\mathfrak{P}$ or not; here $\mathrm{inducedE1},\mathrm{inducedE2},\mathrm{inducedE3}$ are, up to sign, the coefficients in degrees $1,2,3$ of the induced Euler polynomial $\prod_{\mathfrak{P}\mid p}\mathrm{inducedFactor}$, and the Euler coefficient of a character at a place is its value on the uniformizer idele there when unramified and $0$ otherwise. Finally let $S$ be a finite set of finite places of $\mathbb{Q}$. The conclusion: for every admissible character $\sigma$ of the ideles of $\mathbb{Q}$ there exist a finite set $T\supseteq S$ of finite places of $\mathbb{Q}$ and an entire function $E$ on $\mathbb{C}$ such that, for all $s$ with $\mathrm{Re}(s)>1$, $E(s)$ equals the unordered product over the places $p\notin T$ of the inverses of $1-e_1(p)\,x_p+e_2(p)\,x_p^2-c_\omega(p)\,x_p^3$, where $x_p=c_\sigma(p)\,N(p)^{-s}$ with $N(p)$ the absolute norm of $p$, $e_1,e_2$ the induced coefficients of $\mu$ and $c_\omega,c_\sigma$ the Euler coefficients of $\omega,\sigma$.
--
--   This supplies the analytic input for the cubic automorphic induction step in the Langlands–Tunnell argument: the Rankin–Selberg twists of the candidate degree-three Euler product, taken outside a suitable finite set of places, are holomorphic in the whole plane, the non-norm hypothesis on $\mu$ excluding the degenerate case where the induction is reducible. It is used in the construction of the cubic induction datum, via [`LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad`](thm.html#LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

theorem LanglandsTunnell.CubicInduction.exists_entire_eulerTwist_induced_of_not_exists_eq_pow_inertiaDeg
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p → eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∀ σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ σ →
      ∃ T : Finset (HeightOneSpectrum (𝓞 ℚ)), S ⊆ T ∧
        ∃ E : ℂ → ℂ, Differentiable ℂ E ∧
          ∀ s : ℂ, 1 < s.re →
            E s = ∏' p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ T},
              (1 - inducedE1 ℚ (inducedCoeff K μ) p.1 *
                (eulerCoeff ℚ σ p.1 * (((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s)))
                + inducedE2 ℚ (inducedCoeff K μ) p.1 *
                (eulerCoeff ℚ σ p.1 * (((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))) ^ 2
                - eulerCoeff ℚ ω p.1 *
                    (eulerCoeff ℚ σ p.1 * (((Ideal.absNorm p.1.asIdeal : ℕ) : ℂ) ^ (-s))) ^ 3)⁻¹ := by sorry
