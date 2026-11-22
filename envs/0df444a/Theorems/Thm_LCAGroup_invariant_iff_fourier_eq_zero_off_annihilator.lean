-- Prove2me | Theorems.Thm_LCAGroup_invariant_iff_fourier_eq_zero_off_annihilator
-- name    : LCAGroup.invariant_iff_fourier_eq_zero_off_annihilator
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:12.377317+00:00
-- url     : https://prove2.me/theorems/d402b0bf-6870-44b0-9abd-6b50084a2383
-- title:
--   Lemma D.1.5.2(3), corrected — if $f\in L^1(G)$ is $H$-invariant then $\widehat f$ vanishes off $H^\perp$; the converse holds for continuous $f$ with integrable $\widehat f$
-- statement:
--   **Invariance under a subgroup versus support of the Fourier transform** (Lemma D.1.5.2(3), in corrected form).
--
--   Let $G$ be a Hausdorff locally compact abelian group with a (regular) Haar measure $\mu$, let $\widehat G$ be its Pontryagin dual with a (regular) Haar measure $\nu$, and let $H\subseteq G$ be a closed subgroup with annihilator $H^\perp=\{\chi\in\widehat G:\ \chi|_H=1\}$. For $f\in L^1(G,\mu)$ the Fourier transform is
--   $$\widehat f(\chi)=\int_G f(x)\,\overline{\chi(x)}\,d\mu(x),\qquad\chi\in\widehat G .$$
--   Let $f\colon G\to\mathbb C$ be $\mu$-integrable.
--
--   1. If $f$ is $H$-invariant, i.e. $f(xh)=f(x)$ for all $x\in G$ and $h\in H$, then $\widehat f$ vanishes outside $H^\perp$:
--   $$\widehat f(\chi)=0\qquad\text{for all }\chi\in\widehat G\setminus H^\perp .$$
--   2. Conversely, if $f$ is continuous, $\widehat f$ is $\nu$-integrable, and $\widehat f(\chi)=0$ for all $\chi\notin H^\perp$, then $f$ is $H$-invariant: $f(xh)=f(x)$ for all $x\in G$, $h\in H$.
--
--   So for a continuous integrable function with integrable Fourier transform, $H$-invariance is equivalent to $\operatorname{supp}\widehat f\subseteq H^\perp$. For a structural pair $(\Gamma,k)$ and such an $f$, applying this to $H=k$ and, on the dual group, to the function $\widehat f$ and the closed subgroup $\Gamma^\perp\subseteq\widehat G$ (whose annihilator in $G\cong\widehat{\widehat G}$ is $\Gamma$) shows that $f$ is $k$-invariant and supported in $\Gamma$ iff $\widehat f$ is supported in $k^\perp$ and $\Gamma^\perp$-invariant, which is how the Fourier transform exchanges the stages $\mathcal S(k,\Gamma)$ of $\mathcal S(G)$ and $\mathcal S(\Gamma^\perp,k^\perp)$ of $\mathcal S(\widehat G)$.
--
--   **Deviation from the source.** The source asserts the equivalence for every integrable $f$ with integrable Fourier transform. The converse direction is false in that generality (the indicator function of a point of $\mathbb R$ has zero Fourier transform but is not translation invariant); it holds for the continuous representative, because Fourier inversion then holds at every point. Continuity of $f$ is therefore a hypothesis of part 2. Part 1 needs neither continuity nor integrability of $\widehat f$.
--
--   **Formalization Note.** $\widehat f$ is `RiemannMasullo.lcaFourier μ f` and $H^\perp$ is `LCAGroup.annihilator H`. Since $H^\perp$ is closed, "supported in $H^\perp$" is expressed as vanishing at every $\chi\notin H^\perp$. Integrability of $\widehat f$ is with respect to an arbitrary regular Haar measure `ν` on `PontryaginDual G`; all such measures are proportional, so this is the same as integrability for the Plancherel measure.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 761, Lemma D.1.5.2(3)

import Mathlib
import Definitions.Def_RiemannMasullo_LCAFourierConvolution
import Definitions.Def_LCAGroup_Annihilator

open MeasureTheory Topology

set_option autoImplicit false

namespace LCAGroup

theorem invariant_iff_fourier_eq_zero_off_annihilator
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure] [ν.Regular]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (f : G → ℂ) (hf : Integrable f μ) :
    ((∀ x : G, ∀ h ∈ H, f (x * h) = f x) →
      ∀ χ : PontryaginDual G, χ ∉ annihilator H → RiemannMasullo.lcaFourier μ f χ = 0) ∧
    (Continuous f → Integrable (RiemannMasullo.lcaFourier μ f) ν →
      (∀ χ : PontryaginDual G, χ ∉ annihilator H → RiemannMasullo.lcaFourier μ f χ = 0) →
      ∀ x : G, ∀ h ∈ H, f (x * h) = f x) := by sorry

end LCAGroup
