-- Prove2me | Theorems.Thm_OCB2012_cptp_iff_cj
-- name    : OCB2012.cptp_iff_cj
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T09:44:34.543907+00:00
-- url     : https://prove2.me/theorems/62e65f2d-6438-4ed1-9484-880fb4940297
-- title:
--   p. 4: a linear map is CPTP iff its CJ matrix satisfies $M\ge 0$ and $\mathrm{Tr}_{X_2}M = \mathbb 1^{X_1}$
-- statement:
--   Let $\mathcal M : \mathcal L(\mathcal H^{X_1})\to\mathcal L(\mathcal H^{X_2})$ be a linear map between operators on finite-dimensional spaces, and let $M^{X_1X_2} = [\mathcal I\otimes\mathcal M(|\phi^+\rangle\langle\phi^+|)]^T$ be its Choi–Jamiołkowski matrix (p. 3). Then $\mathcal M$ is completely positive and trace preserving if and only if
--
--   $$M^{X_1X_2}\ge 0\qquad\text{and}\qquad \mathrm{Tr}_{X_2}M^{X_1X_2} = \mathbb 1^{X_1}.$$
--
--   The paper uses this equivalence on p. 4 ("Since a map $\mathcal M^A$ is CPTP if and only if its CJ operator satisfies…") to turn the normalization of probabilities into condition (5). It is why the whole mission may represent local operations directly by their CJ matrices. The direction "completely positive $\Rightarrow M\ge0$" and its converse together make up Choi's theorem.
--
--   **Formalization Note.** Complete positivity is `PeresTerno.IsCompletelyPositive`: $\mathcal M\otimes\mathrm{id}_n$ is positive for every finite ancilla dimension $n$. Trace preservation is required for all matrices, which is equivalent to requiring it for all states by linearity.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 3 (CJ matrix) and p. 4 ('Since a map M^A is CPTP if and only if its CJ operator satisfies M^{A1A2} >= 0 and Tr_{A2} M^{A1A2} = 1^{A1}')

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Definitions.Def_OCB2012_cj

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem cptp_iff_cj {x1 x2 : Type*} [Fintype x1] [Fintype x2] [DecidableEq x1] [DecidableEq x2]
    (Φ : Matrix x1 x1 ℂ →ₗ[ℂ] Matrix x2 x2 ℂ) :
    (PeresTerno.IsCompletelyPositive Φ ∧ IsTracePreserving Φ) ↔ IsCPTP_CJ (cjMatrix Φ) := by sorry

end OCB2012
