-- Prove2me | Theorems.Thm_NumberField_Idele_integral_mul_prod_mul_finprod_mul_apply_translate_eq_mul_ideleNorm_partAt_mul_prod_tsum_mul_integral
-- name    : NumberField.Idele.integral_mul_prod_mul_finprod_mul_apply_translate_eq_mul_ideleNorm_partAt_mul_prod_tsum_mul_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/0f3c5f98-d773-5170-837c-f14a816bf8e1
-- title:
--   Centre unfolding of an Euler-bracket idele integrand
-- statement:
--   Let $K$ be a number field, $\nu_{ZK}$ a Haar measure on $(\mathbb{A}_K)^\times$ (with its Borel structure), and $\xi$ a homomorphism from the full subgroup $\top$ of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ such that $z \mapsto \xi(z)$ is continuous as a $\mathbb{C}$-valued function, $\xi$ is trivial on the image of $K^\times$, and, for every finite place $v \notin S$ and every $t \in (K_v)^\times$ with $|t|_v = 1$, $\xi$ kills the idele that is $t$ at $v$ and $1$ elsewhere. Let $S, T$ be finite sets of finite places with $T$ disjoint from $S$, let $PZ$ be product-measure data over $S$ for $\nu_{ZK}$ (constant $c > 0$, measure $\nu_S$, projection, valuation data, off-$S$ triviality, decomposition along uniformiser ideles, and a Fubini–Tonelli identity), whose valuation datum is $v, a \mapsto -\log |a_v|$ and whose projection is truncation of the finite part to $S$, and let $d, u \in K^\times$ with $u \neq 1$. Let $IW, IU$ assign a complex number to an idele and a finite place, let $B$ be complex valued on ideles, and let $IT$ be complex valued on pairs (place, integer), subject to: for $v \in T$ and $w$ a unit at every place outside $S \cup T$ (both $w_v$ and $(w^{-1})_v$ integral there), $IW(w,v) = IT(v, \operatorname{ord}_v w)$; for $v \notin S \cup T$ and every idele $w$, $IU(w,v) = \|u_v - 1\|^{-1}$ if $\|w_v\| = \|u_v\| = 1$ and $0$ otherwise; for $w$ a unit outside $S \cup T$, $B(w) = B$ of the $S$-truncation of $w$; $\xi \cdot B$ is $\nu_S$-integrable; and for $v \in T$ the series $\sum_e \|\xi(\det \mathrm{heckeGen}_v)^e\, IT(v,e)\|$ converges. Then the integral over $(\mathbb{A}_K)^\times$ of $\xi(z) \cdot \big(\prod_{v \in T} IW(zd, v)\big)\big(\prod_{v \notin S \cup T} IU(zd, v)\big) B(zd)$ against $\nu_{ZK}$ equals the product of $c$, the indicator that $\operatorname{ord}_v(u) = 0$ for all $v \notin S \cup T$, the idele norm (the value of the distributive Haar character on $\mathbb{A}_K$) of the $S$-truncation of the principal idele of $u - 1$ when $u - 1 \neq 0$ and $0$ otherwise, the product over $v \in T$ of $\|u_v - 1\|$ times $\sum_{e \in \mathbb{Z}} \xi(\det \mathrm{heckeGen}_v)^e\, IT(v,e)$, and $\int \xi(z_S) B(z_S)\, d\nu_S$.
--
--   This is the unfolding of a single class contribution of an Euler-bracket integrand over the idele class group: the integral of a character times abstract local values, subject only to their three locality laws, is evaluated as a constant times an $S$-integral, a product of local brackets over $T$, and a norm factor coming from the product formula. It is used in the packaging of window terms for automorphic data, and is quoted by [`AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_window_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_ne_one_unweighted`](thm.html#AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_window_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_ne_one_unweighted).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_integral_mul_prod_mul_finprod_mul_apply_translate_eq_mul_ideleNorm_partAt_mul_prod_tsum_mul_integral.lean

import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem NumberField.Idele.integral_mul_prod_mul_finprod_mul_apply_translate_eq_mul_ideleNorm_partAt_mul_prod_tsum_mul_integral
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (hur : ∀ v ∉ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)
    (PZ : UnramifiedWhittaker.ProductMeasureData S νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K S)
    (d : Kˣ)

    (u : Kˣ) (hu1 : (u : K) ≠ 1)

    (IW : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (IU : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (B : (AdeleRing (𝓞 K) K)ˣ → ℂ)

    (IT : HeightOneSpectrum (𝓞 K) → ℤ → ℂ)
    (hWloc : ∀ v ∈ T, ∀ w : (AdeleRing (𝓞 K) K)ˣ, w ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) →
      IW w v = IT v (NumberField.Idele.ord K v w))

    (hUloc : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → ∀ w : (AdeleRing (𝓞 K) K)ˣ,
      IU w v = if ‖(((w : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 ∧ ‖algebraMap K (v.adicCompletion K) (u : K)‖ = 1
        then (((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ))⁻¹ else 0)

    (hBloc : ∀ w : (AdeleRing (𝓞 K) K)ˣ, w ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) →
      B w = B (NumberField.Idele.partAt K S w))

    (hBint : Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * B zS) PZ.νS)

    (hITsum : ∀ v ∈ T, Summable fun e : ℤ =>
      ‖((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * IT v e‖) :
    ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∏ v ∈ T, IW (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d)) v) *
          (∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ S ∪ T), IU (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d)) v) *
          B (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) d))) ∂νZK =
      (PZ.c : ℂ) *
        (if ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0
          then (1 : ℂ) else 0) *
        (if h1 : (u : K) - 1 ≠ 0 then
            ((NumberField.TateGlobal.ideleNorm K
                (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
          else 0) *
        (∏ v ∈ T, ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) *
            ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e *
              IT v e) *
        ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * B zS ∂PZ.νS := by sorry
