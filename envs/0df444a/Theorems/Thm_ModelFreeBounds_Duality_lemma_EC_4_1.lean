-- Prove2me | Theorems.Thm_ModelFreeBounds_Duality_lemma_EC_4_1
-- name    : ModelFreeBounds.Duality.lemma_EC_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:21:40.808635+00:00
-- url     : https://prove2.me/theorems/2ed8b0da-0c6b-4c35-9410-5de966da384b
-- title:
--   Lemma EC.4.1, p. ec16 — under Assumption 2.1 the cone C of payoffs super-replicable at zero cost is closed under pointwise convergence
-- statement:
--   Let $\Omega$ be a Polish space and consider a market with Borel payoffs $g_1,\dots,g_m$ and bid–ask prices $\underline\pi_j\le\overline\pi_j$ satisfying the no-arbitrage Assumption 2.1. Let
--   $$\mathcal C=\{\langle y,g\rangle-\pi(y):y\in\mathbb R^m\}-\mathcal L^0_+$$
--   be the set of payoffs that can be super-replicated at zero initial cost, where $\mathcal L^0_+$ is the set of nonnegative Borel functions on $\Omega$.
--
--   If $(f_n)_{n\ge1}\subset\mathcal C$ and $f_n(\omega)\to f(\omega)$ for every $\omega\in\Omega$, then $f\in\mathcal C$.
--
--   This closedness is what turns approximate superhedging strategies into exact ones; it gives the attainment in Theorem 2.4(ii) and the passage from bounded-above to general payoffs in Theorem 2.4(iii).
--
--   **Formalization Note** Convergence is pointwise at every $\omega$ (there is no reference measure). The limit $f$ is not assumed measurable; membership in $\mathcal C$ requires the representing $h$ to be Borel.
-- source:
--   Neufeld, Papapantoleon & Xiang, Model-free bounds for multi-asset options using option-implied information and their exact computation, arXiv:2006.14288v3, Lemma EC.4.1, p. ec16

import Mathlib
import Definitions.Def_ModelFreeBounds_Duality_Market

open MeasureTheory Filter Topology

namespace ModelFreeBounds.Duality

theorem lemma_EC_4_1 {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    {m : ℕ} (M : Market Ω m) (hM : M.Standing) (hNA : M.NoArbitrage)
    (fn : ℕ → Ω → ℝ) (f : Ω → ℝ) (hfn : ∀ n, fn n ∈ M.superReplicable)
    (hlim : ∀ ω, Tendsto (fun n => fn n ω) atTop (𝓝 (f ω))) :
    f ∈ M.superReplicable := by sorry

end ModelFreeBounds.Duality
