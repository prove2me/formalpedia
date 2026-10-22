-- Prove2me | Theorems.Thm_NetworkQuality_PotentialMax_proposition_1
-- name    : NetworkQuality.PotentialMax.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:08.082551+00:00
-- url     : https://prove2.me/theorems/d7ec91ed-390b-4580-9ea7-ccc1d2f8a0aa
-- title:
--   Proposition 1, p. 10 — under strong network effects the stage-2 equilibria are all-buy, none-buy, or both
-- statement:
--   In the network market under the standing assumptions, fix a quality $q\ge 0$ with strong network effects, i.e. $v_1f(1,q)<v_2f(2,q)<\dots<v_nf(n,q)$. Then for every price $p$ the (pure-strategy) Nash equilibria $B\subseteq N$ of the stage-2 subgame are exactly as follows:
--   1. if $p<v_1f(1,q)$, the only equilibrium is $B=N$ (all consumers buy);
--   2. if $p>v_nf(n,q)$, the only equilibrium is $B=\emptyset$ (no consumer buys);
--   3. if $v_1f(1,q)\le p\le v_nf(n,q)$, the equilibria are exactly $B=N$ and $B=\emptyset$.
--
--   Under strong network effects consumers always coordinate on a common action, and for a range of prices both coordinated outcomes are equilibria; this multiplicity is what makes equilibrium selection matter for the firm.
--
--   **Formalization Note** "Equilibrium" is read as pure-strategy Nash equilibrium of stage 2, identified with the set of buyers, and each case is stated as a characterization of the set of equilibria, which is what the paper's proof establishes. $v_1$ and $v_n$ are the Lean terms `M.v ⟨0, _⟩` and `M.v ⟨n - 1, _⟩`. The hypothesis $q\ge 0$ is the paper's domain of quality.
-- source:
--   Chan, Quality Strategies in Network Markets, SSRN 4203818 (version of April 2023), p. 10, Proposition 1

import Mathlib
import Definitions.Def_NetworkQuality_PotentialMax_Setting

namespace NetworkQuality.PotentialMax

open Market

theorem proposition_1 {n : ℕ} (M : Market n) (hM : M.Standing) (q : ℝ) (hq : 0 ≤ q)
    (hs : M.StrongNE q) (p : ℝ) :
    (p < M.v ⟨0, hM.1⟩ * M.f 1 q →
      ∀ B : Finset (Fin n), M.IsNash B p q ↔ B = Finset.univ) ∧
    (M.v ⟨n - 1, Nat.sub_lt hM.1 Nat.one_pos⟩ * M.f n q < p →
      ∀ B : Finset (Fin n), M.IsNash B p q ↔ B = ∅) ∧
    (M.v ⟨0, hM.1⟩ * M.f 1 q ≤ p → p ≤ M.v ⟨n - 1, Nat.sub_lt hM.1 Nat.one_pos⟩ * M.f n q →
      ∀ B : Finset (Fin n), M.IsNash B p q ↔ (B = Finset.univ ∨ B = ∅)) := by sorry

end NetworkQuality.PotentialMax
