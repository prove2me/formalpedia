-- Prove2me | Theorems.Thm_OCB2012_prob_eq_of_noSignalAtoB
-- name    : OCB2012.prob_eq_of_noSignalAtoB
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-08T23:11:44.506624+00:00
-- url     : https://prove2.me/theorems/6c226e88-b6c4-4ac2-ba13-c016e3e438bb
-- title:
--   With no signalling from Alice to Bob, $W$ sees Alice's operation only through $\mathrm{Tr}_{A_2}M^{A_1A_2}$
-- statement:
--   Let $W^{A_1A_2B_1B_2}$ have the form $W = \mathbb 1^{A_2}\otimes W^{A_1B_1B_2}$. This is the form $W^{A\not\preceq B}$ of p. 4, which the paper calls "the most general situation in which signalling from Alice to Bob is not possible". Let $M^{A_1A_2}$ and $M'^{A_1A_2}$ be operators on Alice's systems with
--
--   $$\mathrm{Tr}_{A_2} M^{A_1A_2} = \mathrm{Tr}_{A_2} M'^{A_1A_2},$$
--
--   and let $M^{B_1B_2}$ be any operator on Bob's systems. Then
--
--   $$\mathrm{Tr}\!\left[W\left(M^{A_1A_2}\otimes M^{B_1B_2}\right)\right] = \mathrm{Tr}\!\left[W\left(M'^{A_1A_2}\otimes M^{B_1B_2}\right)\right].$$
--
--   Every CPTP map of Alice has $\mathrm{Tr}_{A_2}M^{A_1A_2}=\mathbb 1^{A_1}$. So Bob's outcome probabilities do not depend on which CPTP operation Alice performs. This is the mirror image of `OCB2012.prob_eq_of_noSignalBtoA`.
--
--   **Formalization Note.** `IsNoSignalAtoB W` states that $W = \mathbb 1^{A_2}\otimes X^{A_1B_1B_2}$ in the index order `((a1 × a2) × (b1 × b2))`.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 4, paragraph introducing W^{A not-preceq B} = 1^{A2} (x) W^{A1B1B2}

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem prob_eq_of_noSignalAtoB {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (hW : IsNoSignalAtoB W) (MA MA' : Matrix (a1 × a2) (a1 × a2) ℂ)
    (MB : Matrix (b1 × b2) (b1 × b2) ℂ) (h : ptrace₂ MA = ptrace₂ MA') :
    prob W MA MB = prob W MA' MB := by sorry

end OCB2012
