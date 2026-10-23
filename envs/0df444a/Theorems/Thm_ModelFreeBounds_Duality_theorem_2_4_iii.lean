-- Prove2me | Theorems.Thm_ModelFreeBounds_Duality_theorem_2_4_iii
-- name    : ModelFreeBounds.Duality.theorem_2_4_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:36.95598+00:00
-- url     : https://prove2.me/theorems/256aadd6-ccb0-492b-89bb-bbf697383dab
-- title:
--   Theorem 2.4(iii), p. 6 — under Assumption 2.1 the superhedging price ϕ(f) equals sup over μ ∈ Q of ∫ f dμ
-- statement:
--   Let $\Omega$ be a Polish space with its Borel $\sigma$-algebra. Consider a one-period market in which $m$ derivatives with Borel payoffs $g_1,\dots,g_m:\Omega\to\mathbb R$ are traded at bid prices $\underline\pi_j$ and ask prices $\overline\pi_j\ge\underline\pi_j$, and assume no-arbitrage (Assumption 2.1): for every $y\in\mathbb R^m$, if $\langle y,g\rangle-\pi(y)\ge0$ at every point of $\Omega$ then $\langle y,g\rangle-\pi(y)=0$ at every point, where $\pi(y)=\sum_j y_j^+\overline\pi_j-y_j^-\underline\pi_j$.
--
--   Let $f:\Omega\to\mathbb R$ be Borel measurable, let
--   $$\phi(f)=\inf\{c+\pi(y):c\in\mathbb R,\ y\in\mathbb R^m,\ c+\langle y,g\rangle\ge f\}$$
--   be its superhedging price (2.2), and let $\mathcal Q$ be the set of Borel probability measures $\mu$ on $\Omega$ with $\underline\pi_j\le\int_\Omega g_j\,d\mu\le\overline\pi_j$ for $j=1,\dots,m$. Then the superhedging duality (2.3) holds:
--   $$\phi(f)=\sup_{\mu\in\mathcal Q}\int_\Omega f\,d\mu .$$
--
--   The duality identifies the model-free upper price bound of an exotic multi-asset option, a maximisation over all probability measures consistent with the observed bid–ask prices, with the cheapest static superhedge in the traded derivatives, a minimisation over finitely many variables.
--
--   **Formalization Note** Both sides take values in `EReal`: $\phi(f)=+\infty$ when $f$ cannot be superhedged, and the supremum over an empty $\mathcal Q$ is $-\infty$. The paper does not fix a convention for $\int f\,d\mu$ when $f$ is not $\mu$-integrable; here $\int f\,d\mu=\int f^+d\mu-\int f^-d\mu$ with $\infty-\infty=-\infty$ (the duality holds under either convention). Each $g_j$ is required to be $\mu$-integrable for $\mu\in\mathcal Q$, as the real bounds on $\int g_j\,d\mu$ presuppose. No nonemptiness of $\Omega$ is assumed: for $\Omega=\emptyset$ both sides equal $-\infty$.
-- source:
--   Neufeld, Papapantoleon & Xiang, Model-free bounds for multi-asset options using option-implied information and their exact computation, arXiv:2006.14288v3, Theorem 2.4(iii), eq. (2.3), p. 6

import Mathlib
import Definitions.Def_ModelFreeBounds_Duality_Market

open MeasureTheory Filter Topology

namespace ModelFreeBounds.Duality

theorem theorem_2_4_iii {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {m : ℕ} (M : Market Ω m) (hM : M.Standing) (hNA : M.NoArbitrage)
    (f : Ω → ℝ) (hf : Measurable f) :
    M.superhedgingPrice f = ⨆ μ ∈ M.pricingMeasures, expect μ f := by sorry

end ModelFreeBounds.Duality
