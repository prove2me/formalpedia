-- Prove2me | Theorems.Thm_Fundraising_Competition_lemma_2
-- name    : Fundraising.Competition.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:10.15377+00:00
-- url     : https://prove2.me/theorems/715881e3-9e48-4349-b7d5-b9f53d49668f
-- title:
--   Lemma 2, p. 15 — expected donations increase in own effort and base utility, decrease in the others'
-- statement:
--   Consider the competition game with the standing hypotheses, and a profile $(s;x)$ with every effort $x_j \in [0,1]$. HO $i$'s expected donations
--   $$\mathbb E[D_i(s;x)] = z \, x_i \sum_{a \in A_i} w^a_i\, \theta^{J_a}_i(s)$$
--   are
--
--   1. nondecreasing in its own effort $x_i \in [0,1]$;
--   2. nondecreasing in its own base utility $s_i \in \mathbb R$;
--   3. nonincreasing in the effort $x_j \in [0,1]$ of every other HO $j \ne i$;
--   4. nonincreasing in the base utility $s_j \in \mathbb R$ of every other HO $j \ne i$.
--
--   This monotonicity is the behavioural content of the donation model on which the equilibrium analysis rests: contacting more donors and offering a higher base utility help an HO, while its competitors' doing the same hurts it.
--
--   **Formalization Note.** The formula (5) is the definition of expected donations in this formalization, so only the "Furthermore" half of Lemma 2 is a statement. "Increases/decreases" is read weakly (with $x_i = 0$ the donations vanish identically).
-- source:
--   Aflaki, Pedraza-Martinez, Competition and Collaboration on Fundraising for Short-Term Disaster Response: The Impact on Earmarking and Performance, SSRN 3705595 (version of December 2022), p. 15, Lemma 2

import Mathlib
import Definitions.Def_Fundraising_Competition_Setting

namespace Fundraising.Competition

theorem lemma_2 {n : ℕ} (S : Setting n) (hS : Standing S) (s x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    MonotoneOn (fun t => expDonation S s (Function.update x i t) i) (Set.Icc 0 1) ∧
    Monotone (fun t => expDonation S (Function.update s i t) x i) ∧
    (∀ j, j ≠ i → AntitoneOn (fun t => expDonation S s (Function.update x j t) i) (Set.Icc 0 1)) ∧
    (∀ j, j ≠ i → Antitone (fun t => expDonation S (Function.update s j t) x i)) := by sorry

end Fundraising.Competition
