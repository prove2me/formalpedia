-- Prove2me | Theorems.Thm_OpenPitMIP_UltPit_upit_unique_minimal_optimal
-- name    : OpenPitMIP.UltPit.upit_unique_minimal_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:35.404742+00:00
-- url     : https://prove2.me/theorems/ef2aa519-b136-43cf-994a-440247ccacf2
-- title:
--   §4.1 claim (b), p. 1431 — U-PIT admits a unique minimal optimal solution
-- statement:
--   Let $\bar p \in \mathbb R^{\mathcal C}$ be the cluster values $\bar p_c = \sum_{b \in c} \max_{d} p_{b,d}$ of a PCPSP-C instance, and consider the ultimate pit limit problem
--   $$\max \sum_{c \in \mathcal C} \bar p_c x_c \quad \text{s.t.}\quad x_c \le x_{c'}\ \ \forall (c,c') \in \mathcal A, \qquad x_c \in [0,1]\ \ \forall c \in \mathcal C.$$
--   Then U-PIT has exactly one minimal optimal solution: there is a unique optimal $x$ such that every optimal $x' \le x$ (componentwise) equals $x$.
--
--   Theorem 1 speaks of "the" minimal optimal solution of U-PIT; this claim is what makes the article well defined there.
--
--   **Formalization Note** The paper cites this property of maximum closure problems (Hochbaum 2008) rather than proving it. The statement needs at least one destination, so that $\max_d p_{b,d}$ exists. It holds for every instance, with no standing assumption, so none is stated.
-- source:
--   Oper. Res. 68(5), §4.1, claim (b), p. 1431

import Mathlib
import Definitions.Def_OpenPitMIP_UltPit_Setting

namespace OpenPitMIP.UltPit

open PCPSPC

/-- §4.1 claim (b), p. 1431: the ultimate pit limit problem U-PIT (12)–(14) admits a unique
minimal optimal solution. -/
theorem upit_unique_minimal_optimal {B D C : Type} [Fintype B] [Fintype D] [Fintype C]
    [Nonempty D] {T m : ℕ} (I : PCPSPC B D C T m) :
    ∃! x : C → ℝ, I.UPitMinimalOptimal x := by sorry

end OpenPitMIP.UltPit
