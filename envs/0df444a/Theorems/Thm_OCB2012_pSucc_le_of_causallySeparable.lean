-- Prove2me | Theorems.Thm_OCB2012_pSucc_le_of_causallySeparable
-- name    : OCB2012.pSucc_le_of_causallySeparable
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-07T23:08:12.626994+00:00
-- url     : https://prove2.me/theorems/dc7acc29-ee0a-47d9-9837-11662566c62f
-- title:
--   Eq. (2) — causal inequality $p_{succ}\le 3/4$ for causally separable processes
-- statement:
--   Throughout, $A_1,A_2$ (Alice's input and output) and $B_1,B_2$ (Bob's) are finite-dimensional systems; operators on $A_1A_2B_1B_2$ are complex matrices in that tensor order. A CJ matrix $M^{X_1X_2}$ of a CPTP map satisfies $M\ge 0$ and $\operatorname{Tr}_{X_2}M=\mathbb 1^{X_1}$. Let $W$ be **causally separable** (Eq. (6)): $W=q\,W^{B\not\preceq A}+(1-q)\,W^{A\not\preceq B}$ with $0\le q\le 1$, where $W^{B\not\preceq A}=\mathbb 1^{B_2}\otimes W^{A_1A_2B_1}$ and $W^{A\not\preceq B}=\mathbb 1^{A_2}\otimes W^{A_1B_1B_2}$ are process matrices. Let Alice use an instrument $\{M^A(x\mid a)\}_x$ for each input bit $a$, and Bob an instrument $\{M^B(y\mid b,b')\}_y$ for each pair of input bits $(b,b')$ (positive semidefinite CJ matrices whose outcome sums are CPTP). With $a,b,b'$ independent and uniform and $P(x,y\mid a,b,b')=\operatorname{Tr}[W(M^A(x\mid a)\otimes M^B(y\mid b,b'))]$, the success probability of Eq. (1) obeys
--   $$p_{succ}=\tfrac12\big[P(x=b\mid b'=0)+P(y=a\mid b'=1)\big]\le\tfrac34 .$$
--   Dimensions are arbitrary.
--
--   **Formalization Note** The source derives Eq. (2) in an event-based setting (Appendix A) and states on p. 4 that causally separable processes cannot violate it; this item is that process-matrix form. Probabilities are real parts of traces.
-- source:
--   O. Oreshkov, F. Costa, Č. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 2 Eq. (1)–(2); p. 4 Eq. (6) and the sentence following it

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem pSucc_le_of_causallySeparable {a1 a2 b1 b2 : Type*} [Fintype a1] [Fintype a2]
    [Fintype b1] [Fintype b2] [DecidableEq a1] [DecidableEq a2] [DecidableEq b1] [DecidableEq b2]
    (W : Matrix ((a1 × a2) × (b1 × b2)) ((a1 × a2) × (b1 × b2)) ℂ)
    (hW : IsCausallySeparable W)
    (MA : Bool → Bool → Matrix (a1 × a2) (a1 × a2) ℂ) (hMA : IsAliceInstrument MA)
    (MB : Bool → Bool → Bool → Matrix (b1 × b2) (b1 × b2) ℂ) (hMB : IsBobInstrument MB) :
    pSucc W MA MB ≤ 3 / 4 := by sorry

end OCB2012
