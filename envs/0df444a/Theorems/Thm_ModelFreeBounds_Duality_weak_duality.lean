-- Prove2me | Theorems.Thm_ModelFreeBounds_Duality_weak_duality
-- name    : ModelFreeBounds.Duality.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:30.387796+00:00
-- url     : https://prove2.me/theorems/642c4846-5951-4e6a-bf9f-46a7dd0029f8
-- title:
--   Proof of Theorem 2.4(iii), reverse direction, p. ec22 — weak duality ϕ(f) ≥ sup over μ ∈ Q of ∫ f dμ
-- statement:
--   Let $\Omega$ be a Polish space and consider a market with Borel payoffs $g_1,\dots,g_m$ and bid–ask prices $\underline\pi_j\le\overline\pi_j$. Let $f:\Omega\to\mathbb R$ be Borel measurable. Then
--   $$\phi(f)\ \ge\ \sup_{\mu\in\mathcal Q}\int_\Omega f\,d\mu ,$$
--   where $\phi(f)$ is the superhedging price (2.2) and $\mathcal Q$ is the set of Borel probability measures $\mu$ with $\underline\pi_j\le\int g_j\,d\mu\le\overline\pi_j$ for all $j$.
--
--   The no-arbitrage assumption is not needed for this direction. It says that any price below the expected payoff under some pricing measure cannot be the cost of a superhedge.
--
--   **Formalization Note** Both sides take values in `EReal`. $\int_\Omega f\,d\mu=\int f^+d\mu-\int f^-d\mu$ with $\infty-\infty=-\infty$. Each $g_j$ is required to be $\mu$-integrable for $\mu\in\mathcal Q$.
-- source:
--   Neufeld, Papapantoleon & Xiang, Model-free bounds for multi-asset options using option-implied information and their exact computation, arXiv:2006.14288v3, Appendix EC.4, proof of Theorem 2.4(iii), reverse direction, p. ec22

import Mathlib
import Definitions.Def_ModelFreeBounds_Duality_Market

open MeasureTheory Filter Topology

namespace ModelFreeBounds.Duality

theorem weak_duality {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {m : ℕ} (M : Market Ω m) (hM : M.Standing) (f : Ω → ℝ) (hf : Measurable f) :
    ⨆ μ ∈ M.pricingMeasures, expect μ f ≤ M.superhedgingPrice f := by sorry

end ModelFreeBounds.Duality
