-- Prove2me | Theorems.Thm_ModelFreeBounds_Duality_duality_of_bddAbove
-- name    : ModelFreeBounds.Duality.duality_of_bddAbove
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:27.567454+00:00
-- url     : https://prove2.me/theorems/b667c2f0-f6d6-461b-baae-2fda624f0df2
-- title:
--   Proof of Theorem 2.4(iii), pp. ec20–ec22 — the duality ϕ(f) = sup over μ ∈ Q of ∫ f dμ when f is bounded from above
-- statement:
--   Let $\Omega$ be a Polish space and consider a market with Borel payoffs $g_1,\dots,g_m$ and bid–ask prices $\underline\pi_j\le\overline\pi_j$ satisfying the no-arbitrage Assumption 2.1. Let $f:\Omega\to\mathbb R$ be Borel measurable and **bounded from above**. Then
--   $$\phi(f)=\sup_{\mu\in\mathcal Q}\int_\Omega f\,d\mu ,$$
--   where $\phi(f)$ is the superhedging price (2.2) and $\mathcal Q$ is the set of Borel probability measures $\mu$ with $\underline\pi_j\le\int g_j\,d\mu\le\overline\pi_j$ for all $j$.
--
--   This is the first case of the proof of the superhedging duality, obtained in the paper from a semi-infinite Fenchel duality theorem; the general case follows by truncating $f$ from above.
--
--   **Formalization Note** Both sides take values in `EReal`; the supremum over the empty set is $-\infty$. $\int_\Omega f\,d\mu=\int f^+d\mu-\int f^-d\mu$ with $\infty-\infty=-\infty$ (for $f$ bounded above, $\int f^+d\mu<\infty$, so the convention does not arise). Each $g_j$ is required to be $\mu$-integrable for $\mu\in\mathcal Q$.
-- source:
--   Neufeld, Papapantoleon & Xiang, Model-free bounds for multi-asset options using option-implied information and their exact computation, arXiv:2006.14288v3, Appendix EC.4, proof of Theorem 2.4(iii), case f bounded from above, pp. ec20–ec22

import Mathlib
import Definitions.Def_ModelFreeBounds_Duality_Market

open MeasureTheory Filter Topology

namespace ModelFreeBounds.Duality

theorem duality_of_bddAbove {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {m : ℕ} (M : Market Ω m) (hM : M.Standing) (hNA : M.NoArbitrage)
    (f : Ω → ℝ) (hf : Measurable f) (hbdd : BddAbove (Set.range f)) :
    M.superhedgingPrice f = ⨆ μ ∈ M.pricingMeasures, expect μ f := by sorry

end ModelFreeBounds.Duality
