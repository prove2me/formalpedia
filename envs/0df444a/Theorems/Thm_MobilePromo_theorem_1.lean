-- Prove2me | Theorems.Thm_MobilePromo_theorem_1
-- name    : MobilePromo.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:03.196514+00:00
-- url     : https://prove2.me/theorems/ae317898-cdea-4f91-a6f4-4096c91f7bc4
-- title:
--   Theorem 1: BidAlloc has regret at most $K_2K_1^{2T}\sqrt{T}\sqrt{I}$
-- statement:
--   Under Assumptions 1, 2 and 3, the policy BidAlloc satisfies
--
--   $$
--   \mathrm{Regret}(\mathrm{BidAlloc},I;\gamma^{(0)})\le K_3\sqrt I,
--   $$
--
--   where $K_3=K_2K_1^{2T}\sqrt T$ for constants $K_1$ and $K_2$ that are independent of $I$ and $T$.
--
--   Precisely: given the model and the exploration bids, there are $K_1>1$ and $K_2>0$ such that the bound holds for every number of periods $T$, every schedule of seasons, every number of seasons $I$ for which Assumption 3 holds on the first $I$ seasons, every true parameter $\gamma^{(0)}\in\Gamma^{(0)}$, and every choice among likelihood maximizers.
--
--   This is the paper's main upper bound: a policy that does not know the win curves pays $O(\sqrt I)$ more than a clairvoyant over $I$ seasons, in a dynamic program with capacity constraints.
--
--   Differences from the source:
--   - reading: the display of Regret on p.15 and the objective (P) write $\mathbb E\sum(b^\pi_{i,t,l}-e)q_ld_{i,t}$ → the display of p.16: `expCost` is the expectation of the realized cost $\sum(b-e)\mathbb 1\{\zeta_{i,t}=l\}d_{i,t}$; reason: with $d_{i,t}$ the realized win the p.15 display counts $q_l$ twice, and for $L=T=1$, $q<1$ a clairvoyant policy would have regret $(e-b^*)qp(1-q)>0$ per season; the proof uses the p.16 form
--   - encoding: the expectation over random histories → a finite sum over outcome paths `ω : Fin (I * T) → Outcome L` weighted by `pathProb`, seasons 0-based; reason: a period has finitely many outcomes; no instance changes
--   - generalization: constants "independent of $I$ and $T$" → the constants are also chosen before the schedule, the true parameter and the choice among likelihood maximizers; reason: the schedule varies with $I$, so the constants must not see it; the printed proof gives this (compactness of $[b^{\min}-e,0]\times\Gamma^{(0)}\times B$), and it specializes to the printed claim
--   - encoding: "there exist $k_l\in\mathbb N$ and a vector of exploration bids" (Assumption 2, p.12), the input of the policy (p.17) → the bids are the parameter `X : Exploration M`, with $k_l\ge 1$; reason: $\bar b_l$ is an input on p.17, and the phase needs a bid to place
--   - encoding: the policy takes the arg max of the likelihood (p.17) → `bidAlloc` takes an `MLESelector`; reason: the arg max need not be unique
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
--   - encoding: the $I$ seasons of $C_I$ (p.7) → `Schedule T := ℕ → Season T`, of which only the first $I$ are read; reason: the regret, Assumption 3 and the first $IT$ periods of BidAlloc see only seasons $0,\dots,I-1$, and a finite schedule extends; no instance changes
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, Theorem 1, p.18; proof pp.18–20

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_Assumption2
import Definitions.Def_MobilePromo_Assumption3
import Definitions.Def_MobilePromo_bidAlloc

set_option autoImplicit false

namespace MobilePromo

/-- Theorem 1 (SSRN 3523491, Theorem 1, p.18): under Assumptions 1, 2 and 3, the policy `BidAlloc` satisfies
`Regret(BidAlloc, I; γ⁽⁰⁾) ≤ K₃ √I`, where `K₃ = K₂ (K₁)^{2T} √T` for constants `K₁` and `K₂` independent of `I`
and `T`.

**Formalization Note** The order of the quantifiers is the content: `K₁` and `K₂` depend on the model and
the exploration bids only, and are chosen before `T`, `I`, the schedule, the true parameter and the choice
among maximizers of the likelihood. `T ≥ 1` holds because `Season 0` is empty; `I = 0` is trivial. -/
theorem theorem_1 (M : Model) (h1 : Assumption1 M) (X : Exploration M) (h2 : Assumption2 M X) :
    ∃ K₁ K₂ : ℝ, 1 < K₁ ∧ 0 < K₂ ∧
      ∀ (mle : MLESelector M X) {T : ℕ} (S : Schedule T) (I : ℕ), Assumption3 M S I →
        ∀ γ₀ ∈ M.Gamma0,
          regret M S (bidAlloc M X mle S) γ₀ I ≤ K₂ * K₁ ^ (2 * T) * √(T : ℝ) * √(I : ℝ) := by sorry

end MobilePromo
