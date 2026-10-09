-- Prove2me | Theorems.Thm_OCB2012_prob_eq_of_noSignalBtoA
-- name    : OCB2012.prob_eq_of_noSignalBtoA
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-08T23:12:18.175462+00:00
-- url     : https://prove2.me/theorems/f84a80bc-8f26-473c-a4a8-523aeba557be
-- title:
--   With no signalling from Bob to Alice, $W$ sees Bob's operation only through $\mathrm{Tr}_{B_2}M^{B_1B_2}$
-- statement:
--   Let $W^{A_1A_2B_1B_2}$ have the form $W = \mathbb 1^{B_2}\otimes W^{A_1A_2B_1}$. This is the form $W^{B\not\preceq A}$ of p. 4, which describes a situation where Bob cannot signal to Alice. Let $M^{A_1A_2}$ be any operator on Alice's systems. Let $M^{B_1B_2}$ and $M'^{B_1B_2}$ be operators on Bob's systems that have the same reduced operator on his input:
--
--   $$\mathrm{Tr}_{B_2} M^{B_1B_2} = \mathrm{Tr}_{B_2} M'^{B_1B_2}.$$
--
--   Then
--
--   $$\mathrm{Tr}\!\left[W\left(M^{A_1A_2}\otimes M^{B_1B_2}\right)\right] = \mathrm{Tr}\!\left[W\left(M^{A_1A_2}\otimes M'^{B_1B_2}\right)\right].$$
--
--   Every CPTP map has $\mathrm{Tr}_{B_2}M^{B_1B_2}=\mathbb 1^{B_1}$. So the probability of each of Alice's outcomes does not depend on which CPTP operation Bob performs. This is the precise sense in which processes of this form allow no signalling from Bob to Alice. It is the key step behind the causal inequality (2) for one-way processes.
--
--   **Formalization Note.** `IsNoSignalBtoA W` states that $W = \mathbb 1^{B_2}\otimes X^{A_1A_2B_1}$ in the index order `((a1 × a2) × (b1 × b2))`. `ptrace₂` is the partial trace over the second tensor factor.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 4, paragraph introducing W^{A not-preceq B} and the symmetric form W^{B not-preceq A} used in Eq. (6)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem prob_eq_of_noSignalBtoA {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (hW : IsNoSignalBtoA W) (MA : Matrix (a1 × a2) (a1 × a2) ℂ)
    (MB MB' : Matrix (b1 × b2) (b1 × b2) ℂ) (h : ptrace₂ MB = ptrace₂ MB') :
    prob W MA MB = prob W MA MB' := by sorry

end OCB2012
