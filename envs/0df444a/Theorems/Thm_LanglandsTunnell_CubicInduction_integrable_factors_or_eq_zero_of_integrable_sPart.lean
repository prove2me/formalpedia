-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_factors_or_eq_zero_of_integrable_sPart
-- name    : LanglandsTunnell.CubicInduction.integrable_factors_or_eq_zero_of_integrable_sPart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/c87221e1-36b8-5be3-a97a-e782a75460f8
-- title:
--   Integrability of an idelic product forces factorwise integrability or vanishing
-- statement:
--   Let $S$ be a finite set of primes of $\mathbb{Q}$ (height one primes of $\mathcal{O}_{\mathbb{Q}}$), let $\mathrm{finf}$ be a complex-valued function on the idèle group $(\mathbb{A}_{\mathbb{Q}})^{\times}$, and for each prime $v$ let $f_v$ be a complex-valued function on the completion $\mathbb{Q}_v$. Assume that $\mathrm{finf}$ is invariant under [`NumberField.Idele.partAt ℚ ∅`](def/NumberField_IdeleProductMeasure.html#L90), the homomorphism that leaves the infinite component of an idèle untouched and replaces every finite component by $1$; thus $\mathrm{finf}$ depends only on the archimedean part. Assume further that $a \mapsto \mathrm{finf}(a)\prod_{v \in S} f_v(a_v)$ is integrable for the measure [`NumberField.Idele.sPartMeasure ℚ S`](def/NumberField_IdeleProductMeasure.html#L458), the pushforward under the truncation at $S$ of Haar measure on the idèle group restricted to the subgroup of idèles that are units of the local integers at every place outside $S$. Then one of three alternatives holds: either $\mathrm{finf}$ is integrable for `sPartMeasure ℚ ∅` and each $f_v$, $v \in S$, is integrable for the multiplicative measure on $\mathbb{Q}_v^{\times}$ obtained from the self-dual additive Haar measure `selfDualHaarAt ℚ v` (the additive Haar measure on $\mathbb{Q}_v$ giving the local integers volume $(\mathrm{N}v)^{-n_v/2}$, where $n_v$ is the level of the standard local additive character) by restricting to $\{0\}^{\mathsf{c}}$ and multiplying by the density $|x|_v^{-1}$; or $\mathrm{finf}$ vanishes almost everywhere for `sPartMeasure ℚ ∅`; or $f_v$ vanishes almost everywhere for that multiplicative measure for some $v \in S$.
--
--   This is the bookkeeping step that allows a global integral over the $S$-part of the idèle group to be split into an archimedean integral and local integrals at the primes of $S$, in the Tate-style treatment of the local and global zeta integrals used in the Langlands–Tunnell argument. It is invoked by the statements that express the global functional equation as a product of local root numbers times the corresponding evaluation, where the degenerate alternatives (almost-everywhere vanishing of a factor) must be excluded separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integrable_factors_or_eq_zero_of_integrable_sPart.lean

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem LanglandsTunnell.CubicInduction.integrable_factors_or_eq_zero_of_integrable_sPart
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (finf : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ) (f : (v : HeightOneSpectrum (𝓞 ℚ)) → v.adicCompletion ℚ → ℂ)
    (hinf : ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, finf a = finf (NumberField.Idele.partAt ℚ ∅ a))
    (hprod : Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => finf a * ∏ v ∈ S, f v ((a : AdeleRing (𝓞 ℚ) ℚ).2 v))
      (NumberField.Idele.sPartMeasure ℚ S)) :
    (Integrable finf (NumberField.Idele.sPartMeasure ℚ ∅) ∧
        ∀ v ∈ S, letI := LanglandsTunnell.TateLocal.localBorel ℚ v
          Integrable (f v) (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) ∨
      finf =ᵐ[NumberField.Idele.sPartMeasure ℚ ∅] 0 ∨
      ∃ v ∈ S, letI := LanglandsTunnell.TateLocal.localBorel ℚ v;
        f v =ᵐ[LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)] 0 := by sorry
