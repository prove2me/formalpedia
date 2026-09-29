-- Prove2me | Theorems.Thm_NumberField_Idele_integrable_sPartMeasure_of_norm_le_mul_prod
-- name    : NumberField.Idele.integrable_sPartMeasure_of_norm_le_mul_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/0c6ec3f0-4695-5f42-89e3-0440df55caec
-- title:
--   Integrability criterion for the S-part measure via a product majorant
-- statement:
--   Let $F$ be a number field and $S$ a finite set of height-one primes of $\mathcal{O}_F$. Fix a Haar measure $\nu_A$ on the units $(\mathbb{A}_{F,\infty})^\times$ of the infinite adele ring and, for each height-one prime $w$, a measure $\mu_w$ on $(F_w)^\times$, the Borel measurable structures being understood; assume $\mu_w$ is Haar for $w \in S$. Let $f \colon (\mathbb{A}_F)^\times \to \mathbb{C}$, let $g \colon (\mathbb{A}_{F,\infty})^\times \to \mathbb{R}$ and let $h_w \colon (F_w)^\times \to \mathbb{R}$ for each $w$. Suppose $g \ge 0$ and $h_w \ge 0$ for $w \in S$, that $g$ is a.e. strongly measurable and has finite integral for $\nu_A$, that each $h_w$ with $w \in S$ is a.e. strongly measurable and has finite integral for $\mu_w$, and that $f$ is a.e. strongly measurable for the measure [`NumberField.Idele.sPartMeasure F S`](def/NumberField_IdeleProductMeasure.html#L458), the pushforward along `partAt F S` of the idelic Haar measure restricted to the subgroup of idele units whose finite part $\delta$ satisfies $\delta_v, (\delta^{-1})_v \in \mathcal{O}_{F_v}$ for all $v \notin S$. Suppose finally that for every idele unit $a$ whose finite part is $1$ at every $w \notin S$ one has $\|f(a)\| \le g(a_\infty) \prod_{w \in S} h_w(a_w)$, where $a_\infty$ and $a_w$ denote the infinite component and the $w$-component of the finite part of $a$. Then $f$ is integrable for [`NumberField.Idele.sPartMeasure F S`](def/NumberField_IdeleProductMeasure.html#L458).
--
--   This is the integrability half of the factorisation of the $S$-part measure on idele units into an archimedean factor and finitely many local factors at the primes in $S$: a product majorant with integrable factors forces integrability of the whole integrand. It is used in the unfolding computations of the cubic-induction argument, where the dual $S$-part integrand has to be shown integrable before its integral can be evaluated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_Idele_integrable_sPartMeasure_of_norm_le_mul_prod.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_SIdeleClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory

attribute [local instance] NumberField.Idele.ideleBorel in

theorem NumberField.Idele.integrable_sPartMeasure_of_norm_le_mul_prod
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
    (νA : Measure (InfiniteAdeleRing F)ˣ) [νA.IsHaarMeasure]
    [∀ w : HeightOneSpectrum (𝓞 F), MeasurableSpace (w.adicCompletion F)ˣ]
    [∀ w : HeightOneSpectrum (𝓞 F), BorelSpace (w.adicCompletion F)ˣ]
    (μ : ∀ w : HeightOneSpectrum (𝓞 F), Measure (w.adicCompletion F)ˣ)
    (hμ : ∀ w ∈ S, (μ w).IsHaarMeasure)
    (f : (AdeleRing (𝓞 F) F)ˣ → ℂ) (g : (InfiniteAdeleRing F)ˣ → ℝ)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ → ℝ)
    (hg : 0 ≤ g) (hh : ∀ w ∈ S, 0 ≤ h w)
    (hgm : AEStronglyMeasurable g νA) (hhm : ∀ w ∈ S, AEStronglyMeasurable (h w) (μ w))
    (hgi : HasFiniteIntegral g νA) (hhi : ∀ w ∈ S, HasFiniteIntegral (h w) (μ w))
    (hfm : AEStronglyMeasurable f (NumberField.Idele.sPartMeasure F S))
    (hdom : ∀ a : (AdeleRing (𝓞 F) F)ˣ,
      (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → (a : AdeleRing (𝓞 F) F).2 w = 1) →
        ‖f a‖ ≤ g (M4aHerbrand.infPart a) * ∏ w ∈ S, h w (M4aHerbrand.finPart w a)) :
    Integrable f (NumberField.Idele.sPartMeasure F S) := by sorry
