-- Prove2me | Theorems.Thm_InfoBargaining_Monotone_proposition1_optSet_monotone
-- name    : InfoBargaining.Monotone.proposition1_optSet_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:17.799089+00:00
-- url     : https://prove2.me/theorems/9235ed09-d2db-404f-be32-8e1d57dfb112
-- title:
--   Proposition 1, p. 10 — α* increases with θ_b, and first increases and then decreases with c (turning at û)
-- statement:
--   In the base model, let $\mathcal A^*(\theta_b,c)\subseteq[\underline\alpha,\bar\alpha]$ be the set of the buyer's optimal levels of information acquisition, the maximizers of (6)
--   $$U_b(\alpha)=\theta_b\int_c^{\bar v}(v-c)\,dG(v,\alpha)-k(\alpha).$$
--   Write $A\sqsubseteq B$ for the induced (strong) set order: $\min(a,b)\in A$ and $\max(a,b)\in B$ for all $a\in A$, $b\in B$. Then, whenever the two optimal sets compared are nonempty:
--
--   1. **(bargaining power)** for $0<\theta_b\le\theta_b'<1$ and every cost $c$, $\ \mathcal A^*(\theta_b,c)\sqsubseteq\mathcal A^*(\theta_b',c)$;
--   2. **(low cost)** for $\theta_b\in(0,1)$ and $c\le c'\le\hat u$, $\ \mathcal A^*(\theta_b,c)\sqsubseteq\mathcal A^*(\theta_b,c')$;
--   3. **(high cost)** for $\theta_b\in(0,1)$ and $\hat u\le c\le c'$, $\ \mathcal A^*(\theta_b,c')\sqsubseteq\mathcal A^*(\theta_b,c)$.
--
--   That is, the buyer's optimal information acquisition $\alpha^*$ increases with its bargaining power, and first increases and then decreases with the seller's cost, turning at the prior mean $\hat u$.
--
--   The result is the paper's first comparative-statics finding: the seller's cost has a non-monotone (inverted-U) effect on how much information the buyer gathers, which drives the payoff reversals in the rest of the paper.
--
--   **Formalization Note** "$\alpha^*$ increases" is read as the induced set order on the sets of maximizers, the conclusion of Topkis's theorem invoked in the paper's proof; no uniqueness of $\alpha^*$ is assumed. The nonemptiness hypotheses are the paper's presumption that a solution of (6) exists ($k$ is not assumed continuous, so existence is not automatic); without them the set order would hold vacuously. The turning point of "first increases and then decreases" is $c=\hat u$, as in the proof on p. 30; $c=\hat u$ belongs to both ranges.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), p. 10, Proposition 1; proof p. 30

import Mathlib
import Definitions.Def_InfoBargaining_Monotone_Setting
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

namespace InfoBargaining.Monotone

open Supermodularity.Lattices

/-- Proposition 1, p. 10: the buyer's optimal information acquisition `α*` (the set of
maximizers of (6) over `[αlo, αhi]`) increases with its bargaining power `θ_b`, increases
with the seller's cost `c` for `c ≤ û`, and decreases with `c` for `c ≥ û`, each in the
induced (strong) set order and whenever both optimal sets are nonempty. -/
theorem proposition1_optSet_monotone (M : Model) :
    (∀ θb ∈ Set.Ioo (0 : ℝ) 1, ∀ θb' ∈ Set.Ioo (0 : ℝ) 1, ∀ c : ℝ, θb ≤ θb' →
      (M.optSet θb c).Nonempty → (M.optSet θb' c).Nonempty →
      InducedSetOrder (M.optSet θb c) (M.optSet θb' c)) ∧
    (∀ θb ∈ Set.Ioo (0 : ℝ) 1, ∀ c c' : ℝ, c ≤ c' → c' ≤ M.uhat →
      (M.optSet θb c).Nonempty → (M.optSet θb c').Nonempty →
      InducedSetOrder (M.optSet θb c) (M.optSet θb c')) ∧
    (∀ θb ∈ Set.Ioo (0 : ℝ) 1, ∀ c c' : ℝ, M.uhat ≤ c → c ≤ c' →
      (M.optSet θb c).Nonempty → (M.optSet θb c').Nonempty →
      InducedSetOrder (M.optSet θb c') (M.optSet θb c)) := by sorry

end InfoBargaining.Monotone
