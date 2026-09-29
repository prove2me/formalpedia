-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad
-- name    : LanglandsTunnell.CubicInduction.exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/7b4dbc24-1702-5290-bb98-a4956376680c
-- title:
--   Local Whittaker data at bad places of a saturated cubic induction
-- statement:
--   Let $K$ be a cubic number field ($\operatorname{finrank}_{\mathbb Q}K=3$) whose ring of integers is an integral $\mathcal O_{\mathbb Q}$-algebra, let $\mu$ be a character of the idele units of $K$ which is trivial on $K^\times$, continuous and of absolute value $1$, let $S$ be a finite set of primes of $\mathcal O_{\mathbb Q}$ consisting exactly of the places $v$ that are bad for $(K,\mu)$, i.e. some prime above $v$ is ramified or $\mu$ is ramified at some prime above $v$, and let $\omega$ be a character of the idele units of $\mathbb Q$ which is likewise an idele class character, continuous and unitary, which at every good $p$ is unramified with $\omega(\varpi_p)$ equal to minus the coefficient of $X^3$ in $\prod_{\mathfrak P\mid p}\bigl(1-c(\mathfrak P)X^{f(\mathfrak P)}\bigr)$, where $c(\mathfrak P)=\mu(\varpi_{\mathfrak P})$ if $\mu$ is unramified at $\mathfrak P$ and $0$ otherwise, and whose archimedean component at the real place of $\mathbb Q$ is given, whenever the components of $\mu$ at the real places of $K$ have exponents $a_R(w)\in\mathbb Z/2$ and parameters $u_R(w)$ and those at the complex places have parameters $u_C(w)$ and exponents $k_C(w)$, by the parameter $\sum_w u_R(w)+\sum_w 2u_C(w)$ and the exponent $\sum_w a_R(w)+\sum_w (k_C(w)+1)$. Assume saturation at each bad $v$: $\mu$ is ramified at every prime above $v$, and the conductor exponent $t$ of the component $\omega_v$ satisfies $2t+12\le\sum_{w\mid v} f(w)\,\bigl(a(\mu_w)+\mathrm{lev}(\psi_w)\bigr)$, where $a(\mu_w)$ is the conductor exponent of $\mu_w$ and $\mathrm{lev}(\psi_w)$ the level of the standard local additive character. Then for every $v\in S$ and every $\theta\in\mathbb C$ with $\lVert\theta\rVert=1$ there are three locally constant characters $\nu_0,\nu_1,\nu_2$ of $(\mathbb Q_v)^\times$ and natural numbers $a_0,a_1,a_2$ such that $\nu_i$ has conductor exponent $a_i\ge 1$, $\sum_i a_i=\sum_{w\mid v} f(w)(a(\mu_w)+\mathrm{lev}(\psi_w))$, each $\nu_i$ has absolute value $1$ at the standard uniformiser unit, $\nu_0\nu_1\nu_2=\omega_v$, $\prod_i L_v(\nu_i,s)$ equals the inverse of the induced Euler polynomial $\prod_{\mathfrak P\mid v}(1-c(\mathfrak P)X^{f(\mathfrak P)})$ evaluated at $X=N(v)^{-s}$ for all $s$, and $\prod_i \varepsilon_v(\nu_i,\tfrac12)=\theta$; moreover there is $a_\ast\in\mathbb N$ such that for every $c\ge a_\ast$ there exists $W\colon \mathrm{GL}_3(\mathbb Q_v)\to\mathbb C$ with $W(1)=1$, satisfying $W(u(x,y,z)g)=\psi_v(x+y)W(g)$ for the standard local additive character, right invariant under some open subgroup, equivariant at every level $m\ge\sum_i a_i$ in the sense that $W(gk)=\omega_v(u)W(g)$ for $k$ in the congruence set of level $m$ and $u$ the $(2,2)$-entry of $k$, with $\int_{\{\mathrm{v}(x)\le \exp(1)\}}W\bigl(g\,u(0,x,0)\bigr)\,dx=0$ for all $g$ against the self-dual additive Haar measure, admitting $B,t,C$ such that $W$ vanishes off the region where $\det\!\mathrm{size}\cdot\mathrm{lastRowSup}/\mathrm{minorSup}^2\le B$ and $\mathrm{minorSup}/\mathrm{lastRowSup}^2\le B$ and is bounded there by $C$ divided by the $t$-th power of the product of these two quantities, transforming under the centre by $W(zg)=\omega_v(z)W(g)$, and such that for every character $\chi$ of $(\mathbb Q_v)^\times$ of conductor exponent $0$ with $\lVert\chi(\varpi_v)\rVert=1$ and every $g$ in the level-$c$ congruence set there are $P\colon\mathbb C\to\mathbb C$ of the form $P(s)=Q(N(v)^{-s})N(v)^{ms}$ with $Q$ a polynomial and $m\in\mathbb N$, and reals $\sigma_0,\sigma_1$, such that the zeta integral $\mathrm{localZeta30}$ formed from $W,\chi$ against the multiplicative measure converges for $\operatorname{Re}s>\sigma_0$ and equals $\prod_i L_v(\nu_i\chi,s)\,P(s)$ there, the dual integral for $\mathrm{dualWhittakerFn3}\,W$, $\chi^{-1}$ at $\mathrm{weylPrime3}\cdot{}^{t}g^{-1}$ converges for $\operatorname{Re}s>\sigma_1$, and there are conductor exponents $b_i$ of $\nu_i\chi$ with $\mathrm{localZetaDual31}(W,\chi,1-s,g)=\prod_i L_v((\nu_i\chi)^{-1},1-s)\cdot\bigl(\prod_i\varepsilon_v(\nu_i\chi,\tfrac12)\bigr)N(v)^{(\sum_i b_i)(1/2-s)}P(s)$ whenever $\operatorname{Re}(1-s)>\sigma_1$.
--
--   This supplies the local package at the bad primes for the automorphic induction of an idele class character of a cubic field to $\mathrm{GL}_3/\mathbb Q$: at each bad place a triple of ramified local characters with prescribed conductor exponents, prescribed product of $L$-factors and prescribed product of root numbers, together with a local Whittaker function whose zeta integrals satisfy the local functional equation demanded by the $\mathrm{GL}_3$ converse theorem. It is used by [`LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad`](thm.html#LanglandsTunnell.CubicInduction.exists_isCubicInductionDataOn_arch_torusValues_localPackage_bad), which assembles the archimedean, torus and local data into a cubic induction datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda LanglandsTunnell.TateLocal MeasureTheory

theorem LanglandsTunnell.CubicInduction.exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S ↔ IsBadPlace K μ v)
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
    ∀ v ∈ S, ∀ θ : ℂ, ‖θ‖ = 1 →
      ∃ (ν : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (a : Fin 3 → ℕ),
        (∀ i, IsLocallyConstant (ν i)) ∧
        (∀ i, 1 ≤ a i ∧ LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i) (a i)) ∧
        (∑ i, (a i : ℤ)) =
          ∑ᶠ w ∈ primeFibre ℚ K v, (v.asIdeal.inertiaDeg' w.asIdeal : ℤ) * LanglandsTunnell.Converse.pinnedExp K μ w ∧
        (∀ i, ‖((ν i (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1) ∧
        ν 0 * ν 1 * ν 2 = localChar ω v ∧
        (∀ s : ℂ, (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i) s) =
          ((inducedEulerPoly ℚ (inducedCoeff K μ) v).eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))⁻¹) ∧
        (∏ i, LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i)) = θ ∧
        ∃ a₀ : ℕ, ∀ c : ℕ, a₀ ≤ c →
          ∃ W : LocalGL3 v → ℂ,
          W 1 = 1 ∧
          (IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ v) W) ∧
          (∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
        ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g) ∧
          (∀ m : ℕ, (∑ i, a i) ≤ m → IsCongruenceEquivariantAt v m (localChar ω v) W) ∧
          (HasVanishingUnipotentIntegralAt v W) ∧
          (∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
            (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
            (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
              ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)) ∧
          (∀ (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
        W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((localChar ω v z : ℂˣ) : ℂ) * W g) ∧
            ∀ χ : (v.adicCompletion ℚ)ˣ →* ℂˣ, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v χ 0 →
              ‖((χ (NumberField.AdelicLevel.uniformizerUnit ℚ v) : ℂˣ) : ℂ)‖ = 1 →
              ∀ g ∈ converseCongruenceSet3 v c,
                (letI := localBorel ℚ v
    ∃ (P : ℂ → ℂ) (σ₀ σ₁ : ℝ),
      (∃ (Q : Polynomial ℂ) (m : ℕ), ∀ s : ℂ,
        P s = Q.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s)) ∧
      IsLocalZeta30ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
        W χ g σ₀ ∧
      (∀ s : ℂ, σ₀ < s.re →
        localZeta30 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v)))
            W χ s g =
          (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ) s) * P s) ∧
      IsLocalZeta31ConvergentAbove v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
        (dualWhittakerFn3 W)
        χ⁻¹ (weylPrime3 * transposeInv3 g) σ₁ ∧
      ∃ a : Fin 3 → ℕ, (∀ i, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (ν i * χ) (a i)) ∧
        ∀ s : ℂ, σ₁ < (1 - s).re →
          localZetaDual31 v (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) (selfDualHaarAt ℚ v)
              W χ (1 - s) g =
            (∏ i, LanglandsTunnell.TateLocal.localLFactorAt ℚ v (ν i * χ)⁻¹ (1 - s)) *
              ((∏ i, LanglandsTunnell.TateLocal.stdRootNumberAt ℚ v (ν i * χ)) *
                (Ideal.absNorm v.asIdeal : ℂ) ^ ((∑ i, (a i : ℂ)) * (1 / 2 - s))) * P s) := by sorry
