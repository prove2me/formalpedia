-- Prove2me | Theorems.Thm_NumberField_Idele_exists_linearMap_exp_apply_eq_prod_norm_sqrt_mul_zpow_neg_of_apply_det_heckeGen_pow_eq
-- name    : NumberField.Idele.exists_linearMap_exp_apply_eq_prod_norm_sqrt_mul_zpow_neg_of_apply_det_heckeGen_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/122fdd07-3168-538c-9b9d-3646bbde8579
-- title:
--   Tilt modulus along T-units as an exponential linear form
-- statement:
--   Let $K$ be a number field and let $\xi$ be a homomorphism from the full subgroup $\top$ of the idele units $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ such that $z \mapsto \xi(z)$ is continuous as a $\mathbb{C}$-valued function and $\xi$ is trivial on the image of $K^\times$ under the unit map of $K \to \mathbb{A}_K$. Let $S, T$ be finite sets of finite places of $K$ with $T$ disjoint from $S$, and assume $\xi$ is unramified outside $S$ in the sense that for every $v \notin S$ and every unit $t$ of the completion $K_v$ with $\mathrm{v}(t) = 1$, the idele $\mathrm{localUnit}$ equal to $t$ at $v$ and $1$ at all other finite places, with trivial infinite component (`finIncl`), is killed by $\xi$. Let $f : \{\text{finite places}\} \to \mathbb{N}$ with $f_v > 0$ for $v \in T$, let $Nw_v = (\#\mathcal{O}_K/v)^{f_v}$ for $v \in T$, and let $\zeta, s$ be complex-valued with $\zeta_v \neq 0$, $s_v^2 = \zeta_v$ and $\xi\bigl(\det \mathrm{heckeGen}(v)\bigr)^{f_v} = \zeta_v$ for $v \in T$, where $\mathrm{heckeGen}(v)$ is the matrix produced by `diagOne` from the idele that is a uniformiser at $v$ and $1$ elsewhere. Then there is an $\mathbb{R}$-linear form $\ell$ on $\mathbb{R}^r$, $r$ the number of infinite places of $K$, such that for every $\varphi \in K^\times$ whose valuation is $1$ at every finite place outside $T$, and every $k : \mathrm{Fin}\,|T| \to \mathbb{Z}$ satisfying $\mathrm{ord}_{v_j}(\varphi) = f_{v_j} k_j$ for the enumeration $v_j = T.\mathrm{equivFin}^{-1}(j)$, where $\mathrm{ord}_v$ is minus the logarithm of the valuation at $v$ of the finite component of the principal idele, one has $$\exp\Bigl(\ell\bigl(i \mapsto m_{w_i} \log w_i(\varphi)\bigr)\Bigr) = \prod_{j} \bigl\| \sqrt{Nw_{v_j}}\, s_{v_j} \bigr\|^{-k_j},$$ the infinite places being enumerated by `Fintype.equivFin` with $m_w$ their multiplicities.
--
--   This is the computation, in the style of Tate's local–global factorisation of an idele class character, of the modulus of the product $\prod_{v \in T} (\sqrt{Nw_v}\, s_v)^{-k_v}$ along $T$-units: it identifies that modulus with the exponential of a fixed linear form in the logarithmic embedding of $\varphi$. It is used as a hypothesis in the two subsequent statements about sums over units of window integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_exists_linearMap_exp_apply_eq_prod_norm_sqrt_mul_zpow_neg_of_apply_det_heckeGen_pow_eq.lean

import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField.AdelicLevel IsDedekindDomain
open NumberField
open scoped Classical in

theorem NumberField.Idele.exists_linearMap_exp_apply_eq_prod_norm_sqrt_mul_zpow_neg_of_apply_det_heckeGen_pow_eq
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (hur : ∀ v ∉ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)
    (f : HeightOneSpectrum (𝓞 K) → ℕ) (hf : ∀ v ∈ T, 0 < f v)
    (Nw : HeightOneSpectrum (𝓞 K) → ℕ) (hNwf : ∀ v ∈ T, Nw v = Ideal.absNorm v.asIdeal ^ f v)
    (ζ s : HeightOneSpectrum (𝓞 K) → ℂ) (hζ : ∀ v ∈ T, ζ v ≠ 0) (hs : ∀ v ∈ T, s v ^ 2 = ζ v)
    (hx : ∀ v ∈ T,
      ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ f v = ζ v) :
    ∃ ℓ : (Fin (Fintype.card (NumberField.InfinitePlace K)) → ℝ) →ₗ[ℝ] ℝ,
      ∀ φ : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → v.valuationOfNeZero φ = 1) →
        ∀ k : Fin T.card → ℤ,
          (∀ j : Fin T.card,
            NumberField.Idele.ord K (T.equivFin.symm j).1
                (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) φ) =
              (f (T.equivFin.symm j).1 : ℤ) * k j) →
          Real.exp (ℓ fun i => (((Fintype.equivFin (NumberField.InfinitePlace K)).symm i).mult : ℝ) *
              Real.log (((Fintype.equivFin (NumberField.InfinitePlace K)).symm i) (φ : K))) =
            ∏ j : Fin T.card, ‖(Real.sqrt (Nw (T.equivFin.symm j).1 : ℝ) : ℂ) * s (T.equivFin.symm j).1‖ ^ (-(k j)) := by sorry
