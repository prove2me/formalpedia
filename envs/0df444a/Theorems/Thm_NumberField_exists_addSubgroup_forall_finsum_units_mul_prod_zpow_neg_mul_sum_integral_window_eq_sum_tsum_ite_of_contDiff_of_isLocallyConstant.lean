-- Prove2me | Theorems.Thm_NumberField_exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_window_eq_sum_tsum_ite_of_contDiff_of_isLocallyConstant
-- name    : NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_window_eq_sum_tsum_ite_of_contDiff_of_isLocallyConstant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/f10d7700-5812-5db4-9d39-d4e5d2a9e617
-- title:
--   Hyperbolic class sums as finitely many twisted lattice sums
-- statement:
--   Let $K$ be a number field with $r=\#\{\text{infinite places}\}$, let $\nu_{Z_K}$ be a Haar measure on the group of idele units $(\mathbb{A}_K)^\times$, and let $\Xi$ be a finite set of homomorphisms $\xi$ from the full subgroup of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$, each continuous as a $\mathbb{C}$-valued function and trivial on the image of $K^\times$. Let $S_K,T$ be finite sets of finite places with $T$ disjoint from $S_K$ and $2\le\#T$, and assume each $\xi\in\Xi$ is trivial on every idele of the form $t$ at a place $v\notin S_K$ with $|t|_v=1$, trivial elsewhere and with trivial infinite component (i.e. `finIncl` of `localUnit`). Let $f$ be natural numbers with $f_v>0$ on $T$, let $Nw_v=N(v)^{f_v}$ on $T$, and let $\zeta,s$ be complex-valued with $\zeta_v\ne0$, $s_v^2=\zeta_v$ and $\xi(\det \mathrm{heckeGen}_v)^{f_v}=\zeta_v$ for $v\in T$, $\xi\in\Xi$, where $\mathrm{heckeGen}_v$ is the matrix built from a uniformiser at $v$. Let $\Phi_a$ on pairs of points of the mixed space be smooth with compact support, vanishing unless both coordinates correspond to units of the infinite adele ring, with $\mathrm{tsupport}\,\Phi_a$ contained in the image of a compact set $C_a$ of pairs of such units; for each $v\in S_K$ let $\Phi_{f,v}$ on $K_v\times K_v$ be locally constant with compact support, vanishing unless both coordinates are non-zero. Let $C,c'\in\mathbb{C}$. Then there exist: $N\in\mathbb{N}$; a discrete subgroup $\Lambda\le(\mathbb{R}^r)\times\mathbb{Z}^{\#T}$; a linear form $sl$ on $\mathbb{R}^r$ and $\omega\ne0$ in $\mathbb{R}^{\#T}$ with $sl(\gamma_1)=\sum_i\omega_i\gamma_{2,i}$ for all $\gamma\in\Lambda$; a homomorphism $\chi:\Lambda\to(\mathbb{R}/\mathbb{Z})^{r+\#T}$ together with a map $\mathrm{lift}$ to $\mathbb{R}^{r+\#T}$ reducing to $\chi$ modulo $1$ on $\Lambda$; subgroups $\mathrm{sub}_i\le\Lambda$ ($i<N$); smooth functions $G_i$ on $\mathbb{R}^r\times\mathbb{R}^{r+\#T}$ and $R_b\ge0$ such that $G_i$ vanishes when some coordinate of the first argument exceeds $R_b$ in absolute value and $G_i$ is invariant under integer translation in each coordinate of the second argument; and shifts $x_0(i)\in\mathbb{R}^r$, $n_0(i)\in\mathbb{Z}^{\#T}$, $\theta_0(i)\in\mathbb{R}^{r+\#T}$; such that for every $n\in\mathbb{Z}^{\#T}$ one has the identity $$C\sum_{u}\Big(\prod_i(\sqrt{Nw_{v_i}}\,s_{v_i})^{-n_i}\Big)\Big(c'\sum_{\xi\in\Xi}\int \xi(z)\,\Phi_a(u_\infty,z_\infty)\prod_{v\in S_K}\Phi_{f,v}(u_v,z_v)\,d\mu\Big)=\sum_{i<N}\ \sum_{\gamma\in \mathrm{sub}_i}\ [\gamma_2+n_0(i)=n]\;G_i\big(x_0(i)+\gamma_1,\ \theta_0(i)+\mathrm{lift}\,\gamma\big),$$ where the (finitely supported) sum on the left runs over the $u\in K^\times$ with $u\ne1$, with $\mathrm{ord}_v(u)=0$ for all $v\notin S_K\cup T$ and $\mathrm{ord}_{v_i}(u)=f_{v_i}n_i$ for the $i$-th place $v_i$ of $T$ (here $\mathrm{ord}_v$ is minus the logarithm of the $v$-adic valuation of the finite component), $u_\infty$ and $z_\infty$ denote the archimedean components transported to the mixed space, and $\mu$ is the pushforward under $\mathrm{partAt}_{S_K}$ (truncation of the finite part to $1$ outside $S_K$) of $\nu_{Z_K}$ restricted to the subgroup of ideles whose finite components outside $S_K$ are local integral units; the inner sums over $\mathrm{sub}_i$ are infinite sums of the indicated conditional terms.
--
--   This is the number-field core of the winding realisation of the hyperbolic contribution: the class sum over the $(S_K\cup T)$-units of a character-folded family of adelic window integrals is rewritten as a finite collection of smooth, box-supported, periodic lattice sums indexed by sublattices of a discrete subgroup of $\mathbb{R}^r\times\mathbb{Z}^{\#T}$, with explicit shifts and phases. It is used by [`AutomorphicForm.exists_forall_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_eq_sum_tsum_ite_of_smul_eq_map_partAt_of_ne_one`](thm.html#AutomorphicForm.exists_forall_finsum_mul_prod_zpow_neg_mul_ideleNorm_mul_integral_orbital_eq_sum_tsum_ite_of_smul_eq_map_partAt_of_ne_one), where the window integrals arise as twisted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_window_eq_sum_tsum_ite_of_contDiff_of_isLocallyConstant.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem NumberField.exists_addSubgroup_forall_finsum_units_mul_prod_zpow_neg_mul_sum_integral_window_eq_sum_tsum_ite_of_contDiff_of_isLocallyConstant
    (K : Type) [Field K] [NumberField K]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]

    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞc : ∀ ξ ∈ Ξ, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hΞt : ∀ ξ ∈ Ξ, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T SK) (hT2 : 2 ≤ T.card)
    (hur : ∀ ξ ∈ Ξ, ∀ v ∉ SK, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)

    (f : HeightOneSpectrum (𝓞 K) → ℕ) (hf : ∀ v ∈ T, 0 < f v)
    (Nw : HeightOneSpectrum (𝓞 K) → ℕ) (hNwf : ∀ v ∈ T, Nw v = Ideal.absNorm v.asIdeal ^ f v)
    (ζ s : HeightOneSpectrum (𝓞 K) → ℂ) (hζ : ∀ v ∈ T, ζ v ≠ 0) (hs : ∀ v ∈ T, s v ^ 2 = ζ v)
    (hx : ∀ ξ ∈ Ξ, ∀ v ∈ T,
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ f v = ζ v)

    (Φa : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (hΦa_smooth : ContDiff ℝ (⊤ : ℕ∞) Φa) (hΦa_cs : HasCompactSupport Φa)
    (hΦa_units : ∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Φa p ≠ 0 →
      IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1)))
    (Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)) (hCa : IsCompact Ca)
    (hΦa_Ca : ∀ p ∈ tsupport Φa, ∃ q ∈ Ca,
      p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
            InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)])

    (Φf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦf : ∀ v ∈ SK, IsLocallyConstant (Φf v) ∧ HasCompactSupport (Φf v) ∧ ∀ p, Φf v p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0)

    (C c' : ℂ) :
    ∃ (N : ℕ) (Λ : AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), DiscreteTopology Λ ∧
      ∃ (sl : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ) (ω : Fin T.card → ℝ), ω ≠ 0 ∧
        (∀ γ ∈ Λ, sl γ.1 = ∑ i, ω i * (γ.2 i : ℝ)) ∧
      ∃ (χ : Λ →+ (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → AddCircle (1 : ℝ)))
        (lift : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ) → (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)),
        (∀ (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)) (hγ : γ ∈ Λ) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)),
          ((lift γ j : ℝ) : AddCircle (1 : ℝ)) = χ ⟨γ, hγ⟩ j) ∧
      ∃ (sub : Fin N → AddSubgroup ((Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ))), (∀ i, sub i ≤ Λ) ∧
      ∃ (G : Fin N → (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ) → ℂ), (∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) ∧
      ∃ (Rb : ℝ), 0 ≤ Rb ∧
        (∀ i (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)), (∃ k, Rb < |p.1 k|) → G i p = 0) ∧
        (∀ i (p : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ)) (j : Fin (Fintype.card (NumberField.InfinitePlace K) + T.card)), G i (p.1, p.2 + Pi.single j 1) = G i p) ∧
      ∃ (x₀ : Fin N → Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) (n₀ : Fin N → Fin T.card → ℤ) (θ₀ : Fin N → Fin (Fintype.card (NumberField.InfinitePlace K) + T.card) → ℝ),
      ∀ n : Fin T.card → ℤ,
        C *
          ∑ᶠ u ∈ {u : Kˣ | (u : K) ≠ 1 ∧
              (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0) ∧
              ∀ i : Fin T.card, NumberField.Idele.ord K (T.equivFin.symm i).1 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) =
                (f (T.equivFin.symm i).1 : ℤ) * n i},
            (∏ i : Fin T.card, (((Real.sqrt (Nw (T.equivFin.symm i).1 : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^ (-(n i)))) *
            (c' * ∑ ξ ∈ Ξ, ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
                (Φa ![InfiniteAdeleRing.ringEquiv_mixedSpace K
                        (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
                      InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
                  ∏ v ∈ SK, Φf v ((((Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u :
                      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v,
                    (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
                ∂(Measure.map (NumberField.Idele.partAt K SK)
                  (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) =
        ∑ i : Fin N, ∑' γ : sub i,
          if (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).2 + n₀ i = n then
            G i (x₀ i + (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)).1, θ₀ i + lift (γ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) × (Fin T.card → ℤ)))
          else 0 := by sorry
