-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_hasProd_sphericalShellSums_and_globalZeta30_eq_mul_integral_sPart
-- name    : LanglandsTunnell.CubicInduction.exists_hasProd_sphericalShellSums_and_globalZeta30_eq_mul_integral_sPart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/1d0beef6-b681-586e-9adb-245d6ad93c63
-- title:
--   Euler factorisation of the GL₃timesGL₁ zeta integral outside S
-- statement:
--   Let $K$ be a field whose ring of integers is an integral $\mathcal O_{\mathbb Q}$-algebra, let $c$ assign a complex number to each finite place of $K$, let $\psi$ be an additive character of the adeles of $\mathbb Q$ with values in $\mathbb C$, and let $S$ be a finite set of finite places of $\mathbb Q$. Let $W$ be a complex function on $\mathrm{GL}_3$ of the adeles of $\mathbb Q$, $W_\infty$ a function on $\mathrm{GL}_3$ of the infinite adeles, and $W_v$ functions on $\mathrm{GL}_3(\mathbb Q_v)$, subject to: (hfac) for every $x$ and every finite $T \supseteq S$ such that the component of $x$ at each $v \notin T$ lies in `localMaximalCompact3` (all entries of the matrix and of its inverse of valuation $\le 1$), $W(x) = W_\infty(x_\infty)\prod_{v\in T} W_v(x_v)$; (hK) for $v \notin S$, $W_v$ is invariant under right translation by `localMaximalCompact3`; (hlaw) for $v \notin S$, $W_v(u(x,y,z)g) = \psi_v(x+y)W_v(g)$ for all upper unipotent $u(x,y,z)$, where $\psi_v$ is $\psi$ composed with the inclusion of $\mathbb Q_v$ into the adeles at $v$; (hψ0, hψ1) for $v\notin S$, $\psi_v$ is trivial on the elements of valuation $\le 1$ and non-trivial at $\varpi_v^{-1}x$ for some such $x$; (hsph) for $v\notin S$, $W_v$ has the spherical torus values attached to $c$, i.e. $W_v$ at the torus point of exponent $n$ equals $N(v)^{-n}$ times the value at $n$ of the linear recursion `sphericalTorusValue` in the induced coefficients $e_1,e_2,e_3$ of $c$ at $v$, together with the stated two-parameter determinantal values. Let $\chi$ be a homomorphism from the idele units of $\mathbb Q$ to $\mathbb C^\times$ which is trivial on every idele that is $1$ at the archimedean place, $1$ at the places of $S$ and a unit at all finite places; let $g \in \mathrm{GL}_3$ of the adeles have components in the local maximal compacts outside $S$; let $\tau \in \mathbb R$ bound $\|\chi(\varpi_v)\| \le N(v)^{\tau}$ for $v \notin S$, let $\kappa \ge 0$ bound $\|e_i(v)\| \le N(v)^{\kappa}$ ($i=1,2,3$) for $v \notin S$, and let $\sigma_0 \ge \kappa+\tau+4$. Let $H_\nu$ be product measure data `ProductMeasureData` for $S$ and the idelic Haar measure of $\mathbb Q$ (a positive constant $H_\nu.c$, an $S$-part measure $\nu_S$, a projection, order functions and the associated decomposition, Tonelli and measurability properties), and assume that for every $s$ with $\operatorname{Re} s > \sigma_0$ the integrand $a \mapsto W(\iota(\mathrm{diag}(a,1))g)\,\chi(a)\,\|a\|^{s-1}$ is $\nu_S$-integrable. Then there is a function $L$ on $\mathbb C$ such that for every $s$ with $\operatorname{Re} s > \sigma_0$: the family indexed by the places $v \notin S$ of the sums $\sum_{n\ge 0}\mathrm{sphericalTorusValue}(e_1,e_2,e_3)(n)\,(\chi(\varpi_v)N(v)^{-s})^n$ has product $L(s)$; the same integrand is integrable for the idelic Haar measure; and `globalZeta30 W χ s g` equals $H_\nu.c$ times the integral of the integrand against $\nu_S$ times $L(s)$.
--
--   This is the unfolding of the $\mathrm{GL}_3 \times \mathrm{GL}_1$ global zeta integral into an $S$-part integral times an Euler product of unramified local factors, the local factors being the geometric-type series in $\chi(\varpi_v)N(v)^{-s}$ whose coefficients are the spherical torus values attached to $c$. It is used in the cubic-induction comparison of global zeta integrals with products of local root numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_hasProd_sphericalShellSums_and_globalZeta30_eq_mul_integral_sPart.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in

theorem LanglandsTunnell.CubicInduction.exists_hasProd_sphericalShellSums_and_globalZeta30_eq_mul_integral_sPart
    {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (Warch : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (Wloc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (hfac : ∀ (x : AdelicGL 3 (𝓞 ℚ) ℚ) (T : Finset (HeightOneSpectrum (𝓞 ℚ))), S ⊆ T →
      (∀ v, v ∉ T → componentAt3 (𝓞 ℚ) ℚ v x ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v) →
      W x = Warch (archComponent3 (𝓞 ℚ) ℚ x) * ∏ v ∈ T, Wloc v (componentAt3 (𝓞 ℚ) ℚ v x))
    (hK : ∀ v, v ∉ S → ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v, ∀ y : LocalGL3 v, Wloc v (y * k) = Wloc v y)
    (hlaw : ∀ v, v ∉ S → IsGL3PsiWhittakerFn (psiLoc ψ v) (Wloc v))
    (hψ0 : ∀ v, v ∉ S → ∀ x : v.adicCompletion ℚ, Valued.v x ≤ 1 → psiLoc ψ v x = 1)
    (hψ1 : ∀ v, v ∉ S → ∃ x : v.adicCompletion ℚ, Valued.v x ≤ 1 ∧ psiLoc ψ v ((varpi v)⁻¹ * x) ≠ 1)
    (hsph : ∀ v, v ∉ S → HasSphericalTorusValuesAt c v (Wloc v))
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hχU : ∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 ℚ) ℚ).2 v = 1) →
      NumberField.AdeleRing.finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ →
      χ u = 1)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hg : ∀ v, v ∉ S → componentAt3 (𝓞 ℚ) ℚ v g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v)
    (τ : ℝ)
    (hτ : ∀ v, v ∉ S →
      ‖((χ (uniformizerIdele ℚ v) : ℂˣ) : ℂ)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ τ)
    (κ : ℝ) (hκ0 : 0 ≤ κ)
    (hκ : ∀ v, v ∉ S →
      ‖LanglandsTunnell.RankinSelberg.inducedE1 ℚ c v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖LanglandsTunnell.RankinSelberg.inducedE2 ℚ c v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖LanglandsTunnell.RankinSelberg.inducedE3 ℚ c v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (σ₀ : ℝ) (hσ₀ : κ + τ + 4 ≤ σ₀)
    (Hν : UnramifiedWhittaker.ProductMeasureData S (NumberField.Idele.idelicHaar ℚ))
    (hS : ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
        Hν.νS) :
    ∃ L : ℂ → ℂ, ∀ s : ℂ, σ₀ < s.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          (∑' n : ℕ,
            sphericalTorusValue (LanglandsTunnell.RankinSelberg.inducedE1 ℚ c v.1)
                (LanglandsTunnell.RankinSelberg.inducedE2 ℚ c v.1)
                (LanglandsTunnell.RankinSelberg.inducedE3 ℚ c v.1) n *
              (((χ (uniformizerIdele ℚ v.1) : ℂˣ) : ℂ) * cNormQ v.1 ^ (-s)) ^ n))
        (L s) ∧
      Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
          W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1))
        (NumberField.Idele.idelicHaar ℚ) ∧
      globalZeta30 W χ s g =
        (Hν.c : ℂ) *
          (∫ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
            W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) * ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
            ∂Hν.νS) *
          L s := by sorry
