-- Prove2me | Theorems.Thm_LCAGroup_weil_fundamentalDomain_integral
-- name    : LCAGroup.weil_fundamentalDomain_integral
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:21.0688+00:00
-- url     : https://prove2.me/theorems/eaa33a67-fb92-4d27-b64a-14429cc172d4
-- title:
--   Proposition D.1.2.4, eq. (D.1.2.5) — $\int_{G/H}f\,d\bar\mu=\int_\Delta f\circ\pi_H\,d\mu_G$ for a Borel fundamental domain $\Delta$ of a discrete subgroup $H$
-- statement:
--   **Integration over a quotient by a discrete subgroup via a Borel fundamental domain** (second part of Proposition D.1.2.4 of the source).
--
--   Let $G$ be a second countable Hausdorff locally compact abelian group with a Haar measure $\mu_G$, and let $H\subseteq G$ be a closed discrete subgroup, equipped with the counting measure $\mu_H$. Let $\bar\mu$ be the Haar measure on $G/H$ induced by the pair $(\mu_G,\mu_H)$ as in Theorem D.1.2.1, i.e. the Haar measure on $G/H$ with
--   $$\int_G\varphi(g)\,d\mu_G(g)=\int_{G/H}\sum_{h\in H}\varphi(xh)\,d\bar\mu(x)\qquad\text{for all }\varphi\in C_c(G).$$
--   Let $\Delta\subseteq G$ be a Borel set such that the quotient homomorphism $\pi_H\colon G\to G/H$ restricts to a bijection $\Delta\to G/H$ (a *measurable fundamental domain*). Then for every function $f\colon G/H\to\mathbf C$:
--
--   1. $f$ is $\bar\mu$-integrable if and only if $1_\Delta\cdot(f\circ\pi_H)$ is $\mu_G$-integrable;
--   2. in that case
--   $$\int_{G/H}f(\bar g)\,d\bar\mu(\bar g)=\int_\Delta (f\circ\pi_H)(g)\,d\mu_G(g)\qquad\text{(D.1.2.5)}.$$
--
--   In other words, $\bar\mu$ is the image under $\pi_H$ of the restriction of $\mu_G$ to $\Delta$. This is the tool for computing integrals over a quotient by a discrete subgroup, such as $\mathbb A_F/F$, by integrating over a fundamental domain; the source deduces from it that such integrals do not depend on the choice of the fundamental domain (Corollary D.1.2.5). For $G=\mathbb R$, $H=\mathbb Z$, $\Delta=[0,1)$ it is the identity $\int_{\mathbb R/\mathbb Z}f=\int_0^1f(x\bmod 1)\,dx$.
--
--   **Formalization Note.** $\mu_H$ is `Measure.count` on the subgroup `H` (with `[DiscreteTopology H]`), and `ν` is a Haar measure on `G ⧸ H` satisfying the hypothesis `hν`, Weil's formula for continuous compactly supported `φ` with the inner integral `∫ h : H, φ (q.out * h) ∂Measure.count` (the finite sum $\sum_{h\in H}\varphi(xh)$ at the representative `q.out`); this determines `ν`. The fundamental domain is given by `hΔ : MeasurableSet Δ` and `hbij`, bijectivity of `Δ → G ⧸ H`. Integrability of $1_\Delta\cdot(f\circ\pi_H)$ is `IntegrableOn (fun x => f ↑x) Δ μ`. In Lean integrability includes almost-everywhere strong measurability, and `f` is an arbitrary function (no measurability is assumed). The separate measurability equivalence of the source is not restated here; its Borel form is the platform theorem `RiemannMasullo.weilFundamentalDomain_measurable_iff`. The identity (D.1.2.5) is stated without the integrability hypothesis: when $f$ is not integrable both Bochner integrals are $0$ by convention (by part 1), so this is equivalent to the source's formulation. Since $G$ is second countable, all Haar measures involved are automatically regular.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 748, Proposition D.1.2.4 (second part), eq. (D.1.2.5); classical reference: N. Bourbaki, Elements of Mathematics, Integration II, Springer, Ch. VII, §2.10, Theorem 4(c)

import Mathlib

open MeasureTheory Topology

set_option autoImplicit false

namespace LCAGroup

theorem weil_fundamentalDomain_integral
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) [DiscreteTopology H]
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]
    (μ : Measure G) [μ.IsHaarMeasure]
    (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure]
    (hν : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ x ∂μ =
        ∫ q : G ⧸ H, (∫ h : H, φ (q.out * (h : G)) ∂(Measure.count : Measure H)) ∂ν)
    (Δ : Set G) (hΔ : MeasurableSet Δ)
    (hbij : Function.Bijective (fun x : Δ => ((x : G) : G ⧸ H)))
    (f : G ⧸ H → ℂ) :
    (Integrable f ν ↔ IntegrableOn (fun x : G => f (x : G ⧸ H)) Δ μ) ∧
    ∫ q : G ⧸ H, f q ∂ν = ∫ x in Δ, f (x : G ⧸ H) ∂μ := by sorry

end LCAGroup
