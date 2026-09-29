-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated
-- name    : LanglandsTunnell.CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/8b206e9f-aa4a-5369-88e2-335c5ee8ba0b
-- title:
--   Three local characters at a bad prime of cubic induction
-- statement:
--   Let $K$ be a number field with $\mathrm{finrank}_{\mathbb Q} K = 3$, equipped with an integral $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$, let $\mu$ be a character of the idele units of $K$ and $\omega$ one of the idele units of $\mathbb Q$, both admissible twists (continuous, trivial on the principal ideles coming from $K^\times$ resp. $\mathbb Q^\times$, and satisfying `IsUnitaryChar`). Assume, for every height-one prime $p$ of $\mathcal O_{\mathbb Q}$ which is not a bad place for $(K,\mu)$ — bad meaning `IsRamifiedIn K p` or `IsTwistRamifiedAbove K μ p` — that $\omega$ is unramified at $p$ and that its Euler coefficient $\omega(\varpi_p)$ equals $-\,$the coefficient of $X^3$ in the induced Euler polynomial $\prod_{\mathfrak P \mid p} \mathrm{inducedFactor}$ formed from the coefficients $\mathrm{inducedCoeff}\,K\,\mu$ (namely $\mu(\varpi_{\mathfrak P})$ at unramified $\mathfrak P$, and $0$ otherwise); and assume the archimedean matching: whenever the component of $\mu$ at each real place $w$ of $K$ is $x \mapsto \|x\|^{m_w u_R(w)}(x/\|x\|)^{a_R(w)}$ with $a_R(w) \in \mathbb Z/2$ and at each complex place $x \mapsto \|x\|^{m_w u_C(w)}(x/\|x\|)^{k_C(w)}$, then at the real place of $\mathbb Q$ the component of $\omega$ has exponents $\sum_w u_R(w) + \sum_w 2u_C(w)$ and $\sum_w a_R(w) + \sum_w (k_C(w)+1)$ (finite sums over real resp. complex places). Assume finally the saturation hypothesis: at every bad prime $v$, $\mu$ is ramified at every prime $w$ of $K$ with $w$ lying in the fibre over $v$, and the local component $\omega_v$ has some conductor exponent $t$ with $2t + 12 \le S_v := \sum_{w \mid v} f(w/v)\,\mathrm{pinnedExp}\,K\,\mu\,w$, where $\mathrm{pinnedExp}$ is the conductor exponent of $\mu_w$ plus the level of the standard additive character at $w$. Then for every bad prime $v$ and every $\theta \in \mathbb C$ with $|\theta| = 1$ there are three characters $\nu_0,\nu_1,\nu_2$ of $(\mathbb Q_v)^\times$ and naturals $a_0,a_1,a_2$ such that each $\nu_i$ is locally constant, $a_i \ge 1$ is a conductor exponent of $\nu_i$, $\sum_i a_i = S_v$, $|\nu_i(\varpi_v)| = 1$, $\nu_0\nu_1\nu_2 = \omega_v$, $\prod_i L_v(\nu_i,s)$ equals the inverse of the induced Euler polynomial at $v$ evaluated at $N(v)^{-s}$ for all $s$, and $\prod_i \varepsilon_v(\nu_i,1/2) = \theta$.
--
--   This supplies the local data at the bad primes for the converse-theorem construction underlying cubic automorphic induction: three local characters whose product is the prescribed central character component, whose local $L$-factors reconstruct the induced Euler factor, and whose standard root numbers can be made to multiply to any prescribed unimodular constant. It is used in the assembly of the global automorphy datum, via [`LanglandsTunnell.CubicInduction.exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda

theorem LanglandsTunnell.CubicInduction.exists_prod_eq_localChar_and_prod_stdRootNumberAt_eq_of_saturated
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (hsat : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v →
      (∀ w ∈ primeFibre ℚ K v, ¬ IsUnramifiedCharAt μ w) ∧
        ∃ t : ℕ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar ω v) t ∧
          2 * (t : ℤ) + 12 ≤
            ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w)
    :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K μ v → ∀ θ : ℂ, ‖θ‖ = 1 →
      ∃ (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → ℕ),
        (∀ i, IsLocallyConstant (ν i)) ∧
        (∀ i, 1 ≤ a i ∧ LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i) (a i)) ∧
        (∑ i, (a i : ℤ)) =
          ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w ∧
        (∀ i, ‖((ν i (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) ∧
        ν 0 * ν 1 * ν 2 = localChar ω v ∧
        (∀ s : ℂ, (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i) s) =
          ((inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹) ∧
        (∏ i, LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i)) = θ := by sorry
