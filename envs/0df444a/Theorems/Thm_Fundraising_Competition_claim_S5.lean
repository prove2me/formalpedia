-- Prove2me | Theorems.Thm_Fundraising_Competition_claim_S5
-- name    : Fundraising.Competition.claim_S5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:17.429611+00:00
-- url     : https://prove2.me/theorems/fec77a72-e171-4757-8447-1aa1d7e3e9c2
-- title:
--   Claim (S5), proof of Proposition 1, p. S10 — HO i's best response maximizes PPD_i over s_i and sets x_i = min(B_i/PPD_i, 1)
-- statement:
--   Consider the competition game with the standing hypotheses and a profile $(s;x) \in \prod_j [a_j,b_j] \times [0,1]^n$. For every HO $i$, its own strategy $(s_i, x_i)$ solves its lexicographic problem (6) against $(s_{-i}, x_{-i})$ if and only if
--
--   1. $s_i$ maximizes $\sigma \mapsto PPD_i((s_{-i}, \sigma); x)$ over $[a_i, b_i]$, where $PPD_i(s;x) = \delta_i(s_i)\, z \sum_{a\in A_i} w^a_i\, \theta^{J_a}_i(s)$; and
--   2. $$x_i = \min\left(\frac{B_i}{PPD_i(s;x)},\, 1\right).$$
--
--   This is the claim at the start of the proof of Proposition 1: the two-level problem (6) reduces to maximizing the unit performance per donor contacted, after which the effort is the smallest one that closes the funding gap (or full effort if the gap cannot be closed). It is the bridge between the equilibrium definition and the system (7).
--
--   **Formalization Note.** The page states the claim as "in equilibrium, HO $i$ solves (S5)"; its proof shows both directions, which is what is stated here. $B_i > 0$ is a standing hypothesis (with $B_i = 0$ every $s_i$ is a best response and direction "only if" fails). The paper writes $\delta(s_i)$ for $\delta_i(s_i)$.
-- source:
--   Aflaki, Pedraza-Martinez, Competition and Collaboration on Fundraising for Short-Term Disaster Response: The Impact on Earmarking and Performance, SSRN 3705595 (version of December 2022), p. S10 (PDF 43), proof of Proposition 1, claim (S5)

import Mathlib
import Definitions.Def_Fundraising_Competition_Setting

namespace Fundraising.Competition

theorem claim_S5 {n : ℕ} (S : Setting n) (hS : Standing S) (s x : Fin n → ℝ)
    (hbox : InProfileBox S s x) (i : Fin n) :
    IsBestResponse S s x i (s i, x i) ↔
      (IsMaxOn (fun σ => PPD S (Function.update s i σ) x i) (Set.Icc (S.a i) (S.b i)) (s i) ∧
        x i = min (S.B i / PPD S s x i) 1) := by sorry

end Fundraising.Competition
