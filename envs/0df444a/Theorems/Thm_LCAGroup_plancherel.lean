-- Prove2me | Theorems.Thm_LCAGroup_plancherel
-- name    : LCAGroup.plancherel
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:59.204197+00:00
-- url     : https://prove2.me/theorems/346c67c5-fbf2-44a7-b656-58b656939839
-- title:
--   Lemma D.1.1.2(4) — Plancherel theorem for a locally compact abelian group: unique Plancherel measure and the unitary $\mathcal F_G\colon L^2(G)\to L^2(\widehat G)$
-- statement:
--   **Plancherel theorem for locally compact abelian groups** (Lemma D.1.1.2(4) of the source).
--
--   Let $G$ be a Hausdorff locally compact abelian group with a Haar measure $\mu_G$, let $\widehat G$ be its Pontryagin dual, and let $\widehat f(\chi)=\int_G f(x)\overline{\chi(x)}\,d\mu_G(x)$ be the Fourier transform of $f\in L^1(G,\mu_G)$. Then:
--
--   1. there is a **unique** Haar measure $\mu_{\widehat G}$ on $\widehat G$, the *Plancherel measure*, such that for every $f\in L^1(G,\mu_G)\cap L^2(G,\mu_G)$ the transform $\widehat f$ lies in $L^2(\widehat G,\mu_{\widehat G})$ and
--   $$\|f\|_2=\|\widehat f\|_2 ;$$
--   2. the Fourier transform $f\mapsto\widehat f$ on $L^1\cap L^2$ extends uniquely to a unitary isomorphism of Hilbert spaces
--   $$\mathcal F_G\colon L^2(G,\mu_G)\xrightarrow{\ \sim\ }L^2(\widehat G,\mu_{\widehat G}),$$
--   i.e. a surjective $\mathbb C$-linear isometry.
--
--   This is the $L^2$-theory of the Fourier transform on $G$; for $G=\mathbb R^n$ it is the classical Plancherel theorem and for compact or discrete $G$ it is Parseval's identity. The Plancherel measure is the normalisation of Haar measure on $\widehat G$ used in the Fourier inversion formula and in the Poisson summation formula (Situation D.1.2.6 of the source).
--
--   **Formalization Note.** `LCAGroup.IsPlancherelMeasure μ ν` (definition `LCAGroup_PlancherelMeasure`) says that `ν` is a regular Haar measure on `PontryaginDual G` with `eLpNorm f̂ 2 ν = eLpNorm f 2 μ` (and `MemLp f̂ 2 ν`) for all integrable $f\in L^2$, where `f̂ = RiemannMasullo.lcaFourier μ f`. Part 1 is `∃! ν, IsPlancherelMeasure μ ν`: uniqueness among regular Haar measures on the Borel $\sigma$-algebra of $\widehat G$ (binders `[MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]`, since Mathlib has no default $\sigma$-algebra there). Part 2 says that for every such `ν` there is a unique linear isometric equivalence `U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν` such that, for every $f$ with `Integrable f μ` and `h₂ : MemLp f 2 μ`, the class `U (h₂.toLp f)` is represented `ν`-almost everywhere by $\widehat f$. Haar measures are regular (`IsHaarMeasure` together with Mathlib's `Measure.Regular`), i.e. Haar measures in the classical Radon sense of the cited references; regularity is automatic when $G$ is second countable. $G$ carries its Borel $\sigma$-algebra (`[BorelSpace G]`), and groups are written multiplicatively.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 747, Lemma D.1.1.2(4), eqs. (D.1.1.9)–(D.1.1.10); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Theorem 3.4.8 and p. 77

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Definitions.Def_LCAGroup_PlancherelMeasure

open MeasureTheory Topology

set_option autoImplicit false

namespace LCAGroup

theorem plancherel
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    (∃! ν : Measure (PontryaginDual G), IsPlancherelMeasure μ ν) ∧
    ∀ ν : Measure (PontryaginDual G), IsPlancherelMeasure μ ν →
      ∃! U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν,
        ∀ (f : G → ℂ) (_hf : Integrable f μ) (h₂ : MemLp f 2 μ),
          (U (h₂.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] RiemannMasullo.lcaFourier μ f := by sorry

end LCAGroup
