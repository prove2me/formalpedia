-- Prove2me | Theorems.Thm_OCB2012_pSucc_le_of_noSignalBtoA
-- name    : OCB2012.pSucc_le_of_noSignalBtoA
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-08T23:11:58.250967+00:00
-- url     : https://prove2.me/theorems/75d595e1-3852-4802-bee6-8123acd41f4b
-- title:
--   Eq. (2) for one-way processes $W^{B\not\preceq A}$: $p_{succ}\le 3/4$
-- statement:
--   Let $W$ be a process matrix (conditions (4)–(5)) on $A_1A_2B_1B_2$, of any finite dimensions. Suppose $W$ has the one-way form $W^{B\not\preceq A} = \mathbb 1^{B_2}\otimes W^{A_1A_2B_1}$ (no signalling from Bob to Alice). Alice and Bob play the game of Eq. (1). The bits $a, b, b'$ are independent and uniform. Alice guesses $x$ using an instrument that depends on $a$. Bob guesses $y$ using an instrument that depends on $(b, b')$. Then
--
--   $$p_{succ} = \tfrac12\left[P(x=b\mid b'=0) + P(y=a\mid b'=1)\right] \;\le\; \tfrac34 .$$
--
--   This is the causal inequality (2) for each of the two definite causal orders that appear in Eq. (6). The paper notes on p. 4 that if all events are localized in a causal structure, then at most unidirectional signalling between the laboratories is allowed. It also notes there that causally separable processes cannot be used to violate (2). With the mirror statement for the other order, this gives Eq. (2) for every causally separable process (milestone `OCB2012.pSucc_le_of_causallySeparable`).
--
--   **Formalization Note.** An instrument is a family of positive semidefinite CJ matrices, indexed by the guess and the inputs, whose sum over the guess is the CJ matrix of a CPTP map. `pSucc` is Eq. (1) with uniform bits. Its probabilities are the real parts of $\mathrm{Tr}[W(M^A\otimes M^B)]$.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 3 Eq. (2) and p. 4 (paragraph before Eq. (6) on unidirectional signalling; paragraph after Eq. (6): causally separable processes cannot be used to violate the causal inequality (2))

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem pSucc_le_of_noSignalBtoA {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ) (hW : IsProcessMatrix W) (hf : IsNoSignalBtoA W)
    (MA : Bool → Bool → Matrix (a1 × a2) (a1 × a2) ℂ) (hMA : IsAliceInstrument MA)
    (MB : Bool → Bool → Bool → Matrix (b1 × b2) (b1 × b2) ℂ) (hMB : IsBobInstrument MB) :
    pSucc W MA MB ≤ 3 / 4 := by sorry

end OCB2012
