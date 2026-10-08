-- Prove2me | Theorems.Thm_OCB2012_causal_inequality_violation
-- name    : OCB2012.causal_inequality_violation
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-07T23:12:59.705313+00:00
-- url     : https://prove2.me/theorems/88ae417e-6638-4765-88b5-ee8b734292a4
-- title:
--   Violation of the causal inequality: a four-qubit process with $p_{succ}>3/4$
-- statement:
--   There exist a four-qubit **process matrix** $W$ on $A_1A_2B_1B_2$ (Eqs. (4)–(5)), a local instrument $\{M^A(x\mid a)\}_x$ for Alice for each input bit $a$, and a local instrument $\{M^B(y\mid b,b')\}_y$ for Bob for each pair of input bits $(b,b')$ (positive semidefinite CJ matrices whose outcome sums are CJ matrices of CPTP maps) such that the success probability of the task of Eq. (1),
--   $$p_{succ}=\tfrac12\big[P(x=b\mid b'=0)+P(y=a\mid b'=1)\big],\qquad P(x,y\mid a,b,b')=\operatorname{Tr}\big[W(M^A(x\mid a)\otimes M^B(y\mid b,b'))\big],$$
--   with $a,b,b'$ independent and uniform, **strictly exceeds** the causal bound: $p_{succ}>3/4$.
-- source:
--   O. Oreshkov, F. Costa, Č. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, Abstract; p. 5, Eqs. (2), (7), (8)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem causal_inequality_violation :
    ∃ (W : Matrix ((Qubit × Qubit) × (Qubit × Qubit)) ((Qubit × Qubit) × (Qubit × Qubit)) ℂ)
      (MA : Bool → Bool → Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ)
      (MB : Bool → Bool → Bool → Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ),
      IsProcessMatrix W ∧ IsAliceInstrument MA ∧ IsBobInstrument MB ∧
        3 / 4 < pSucc W MA MB := by sorry

end OCB2012
