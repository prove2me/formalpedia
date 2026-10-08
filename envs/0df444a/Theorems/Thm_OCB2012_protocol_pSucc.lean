-- Prove2me | Theorems.Thm_OCB2012_protocol_pSucc
-- name    : OCB2012.protocol_pSucc
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-07T23:10:10.916984+00:00
-- url     : https://prove2.me/theorems/81ed8666-7b00-438a-83fb-11c5033a0163
-- title:
--   Eq. (8) — the protocol of Appendix E achieves $p_{succ}=(2+\sqrt2)/4$
-- statement:
--   Let $\rho^{B_2}$ be any qubit density matrix. Alice's CJ matrices are $\xi(x,a)=\tfrac14[\mathbb 1+(-1)^x\sigma_z]^{A_1}\otimes[\mathbb 1+(-1)^a\sigma_z]^{A_2}$ (Eq. (20)). Bob's are $\eta(y,b,b')=b'\,\eta_1(y,b)+(b'\oplus1)\,\eta_2(y,b)$ with $\eta_1(y,b)=\tfrac12[\mathbb 1+(-1)^y\sigma_z]^{B_1}\otimes\rho^{B_2}$ and $\eta_2(y,b)=\tfrac14[\mathbb 1+(-1)^y\sigma_x]^{B_1}\otimes[\mathbb 1+(-1)^{b+y}\sigma_z]^{B_2}$ (Eqs. (21)–(23)). Then $\{\xi(x,a)\}_x$ and $\{\eta(y,b,b')\}_y$ are local instruments (positive semidefinite, with CPTP outcome sums), and with the process matrix $W$ of Eq. (7) the success probability of Eq. (1) is
--   $$p_{succ}=\frac{2+\sqrt2}{4}.$$
-- source:
--   O. Oreshkov, F. Costa, Č. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 5, Eq. (8); Appendix E, Eqs. (20)–(23)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem protocol_pSucc (ρ : Matrix Qubit Qubit ℂ) (hρ : PeresTerno.IsDensityMatrix ρ) :
    IsAliceInstrument ξ ∧ IsBobInstrument (η ρ) ∧
      pSucc W7 ξ (η ρ) = (2 + Real.sqrt 2) / 4 := by sorry

end OCB2012
