-- Prove2me | Theorems.Thm_LiquidDemocracy_Upward_urn_coupling
-- name    : LiquidDemocracy.Upward.urn_coupling
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:25:15.682628+00:00
-- url     : https://prove2.me/theorems/de1def5c-a506-45bb-bd33-58ddd05ba448
-- title:
--   Proof of Theorem 1, p. 16 — under M^U_p the component sizes of G_n have the law of the Pólya urn's bin sizes, and max-weight(G_n) that of L^p_n
-- statement:
--   Let $p\in(0,1)$, let $\mathcal D$ be a continuous distribution supported in $[0,1]$, and let $n\ge1$. Draw the instance $(\vec p_n,G_n)$ from $\mathbb P_{\mathcal D,M^U_p,n}$, the law of the Upward Delegation Model. Then
--
--   1. the multiset of component sizes of $G_n$ (the weights of the voters who vote directly) has the same distribution as the multiset of bin sizes of the infinite Pólya urn with attachment probability $p$ after $n$ steps;
--   2. consequently, for every $x$,
--   $$\mathbb P_{\mathcal D,M^U_p,n}\big[\text{max-weight}(G_n)\le x\big]=\Pr\big[L^p_n\le x\big].$$
--
--   Combined with Lemma 2, this shows that the Upward Delegation Model satisfies condition (1) of Lemma 1.
--
--   **Formalization Note** Equality in distribution is stated event by event: for every set $S$ of multisets, the two probabilities of landing in $S$ agree. The page conditions on the probability-one event that all competencies differ; this is not a hypothesis here, since continuity of $\mathcal D$ makes it almost sure.
-- source:
--   Berinsky et al., Tracking Truth with Liquid Democracy, arXiv:2107.11868v3, p. 16, proof of Theorem 1, 'Upward Delegation satisfies (1)'

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Setting
import Definitions.Def_LiquidDemocracy_Upward_Urn

namespace LiquidDemocracy.Upward

open MeasureTheory

/-- Proof of Theorem 1, p. 16: for `p ∈ (0,1)`, a continuous `𝒟` and `n ≥ 1` voters, the component
sizes of `G_n` under `ℙ_{𝒟,M^U_p,n}` have the same distribution as the bin sizes of the Pólya urn with
attachment probability `p` after `n` steps, and hence `max-weight(G_n)` has the law of `L^p_n`. -/
theorem urn_coupling (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (D : Measure ℝ) (hD : D ∈ ContClass)
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ S : Set (Multiset ℕ), (instanceLaw D (upward p) n).real {ω | compSizes ω.2 ∈ S} =
        (urnLaw p n).real {s | (s : Multiset ℕ) ∈ S}) ∧
      ∀ x : ℕ, (instanceLaw D (upward p) n).real {ω | maxWeight ω.2 ≤ x} =
        (urnLaw p n).real {s | maxBin s ≤ x} := by sorry

end LiquidDemocracy.Upward
