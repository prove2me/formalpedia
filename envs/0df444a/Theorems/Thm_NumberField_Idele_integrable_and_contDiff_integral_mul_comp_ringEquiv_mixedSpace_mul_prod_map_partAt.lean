-- Prove2me | Theorems.Thm_NumberField_Idele_integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt
-- name    : NumberField.Idele.integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/3fe8705d-b4be-55d4-bd97-592468af4b78
-- title:
--   Smoothness of ξ-twisted adelic window integrals in the archimedean parameter
-- statement:
--   Let $K$ be a number field, and equip the idele group $(\mathbb A_K)^\times$ with a measurable structure that is Borel for its topology; let $\nu$ be a Haar measure on it. Fix a finite set $S$ of finite places of $K$, a continuous function $\xi:(\mathbb A_K)^\times\to\mathbb C$, and a function $G$ on $\mathrm{mixedSpace}(K)\times\mathrm{mixedSpace}(K)$ that is $C^\infty$ over $\mathbb R$ (smoothness of every order) and has compact support, together with a compact set $Ca$ of units of the infinite adele ring such that $G(x,\rho(y))\neq 0$ forces $y$ to lie in the image of $Ca$ under $\mathrm{Units.val}$, where $\rho=$ `InfiniteAdeleRing.ringEquiv_mixedSpace K`. Fix also, for every finite place $v$, a function $\Phi_v$ on $K_v\times K_v$, assumed for $v\in S$ to be locally constant, compactly supported, and such that $\Phi_v(p)\neq 0$ implies both coordinates of $p$ are nonzero, and fix $b_v\in K_v$ for every finite place $v$. Let $\nu_S$ be the push-forward, along the homomorphism on unit ideles induced by the map of adeles which keeps the archimedean component and applies the $S$-truncation `truncFin` to the finite component, of the restriction of $\nu$ to the subgroup of unit ideles $\delta$ whose finite component at every $v\notin S$ lies in $\mathcal O_{K_v}$ along with that of $\delta^{-1}$. Then: for each $x\in\mathrm{mixedSpace}(K)$ the function $z\mapsto \xi(z)\,\bigl(G(x,\rho(z_\infty))\prod_{v\in S}\Phi_v(b_v,z_v)\bigr)$ is $\nu_S$-integrable, and the function sending $x$ to the corresponding integral is $C^\infty$ over $\mathbb R$ on $\mathrm{mixedSpace}(K)$.
--
--   This is the parametric-integral input of the idelic part of the argument: it says that folding a smooth compactly supported archimedean window against finite local windows over the $(S\cup\infty)$-part measure produces a smooth function of the archimedean parameter. It is obtained from a general smoothness theorem for parametric integrals of the form $x\mapsto\int h(a)G(x,\pi(a))$ together with the compactness of the relevant idelic box, and it is used in the evaluation of the window integrals and the resulting sum formulae over unit ideles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

open scoped Classical in

theorem NumberField.Idele.integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (AdeleRing (𝓞 K) K)ˣ → ℂ) (hξc : Continuous ξ)
    (G : mixedEmbedding.mixedSpace K × mixedEmbedding.mixedSpace K → ℂ)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G)
    (Ca : Set (InfiniteAdeleRing K)ˣ) (hCa : IsCompact Ca)
    (hG0 : ∀ (x : mixedEmbedding.mixedSpace K) (y : InfiniteAdeleRing K),
      G (x, InfiniteAdeleRing.ringEquiv_mixedSpace K y) ≠ 0 → y ∈ Units.val '' Ca)
    (Φf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦf : ∀ v ∈ S, IsLocallyConstant (Φf v) ∧ HasCompactSupport (Φf v) ∧
      ∀ p, Φf v p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0)
    (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) :
    (∀ x : mixedEmbedding.mixedSpace K,
      Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ξ zS *
          (G (x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)))
        (Measure.map (NumberField.Idele.partAt K S)
          (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun x : mixedEmbedding.mixedSpace K =>
      ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ξ zS *
          (G (x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1) *
            ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
        ∂(Measure.map (NumberField.Idele.partAt K S)
          (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) := by sorry
