-- Prove2me | Theorems.Thm_OCB2012_isTracePreserving_iff_ptrace_cj
-- name    : OCB2012.isTracePreserving_iff_ptrace_cj
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-09T10:14:22.275381+00:00
-- url     : https://prove2.me/theorems/2c8b8adf-f8c0-4835-9658-a90c84e1f36c
-- title:
--   A linear map is trace preserving iff its CJ matrix satisfies $\mathrm{Tr}_{X_2} M^{X_1X_2} = \mathbb 1^{X_1}$
-- statement:
--   Let $\Phi: \mathcal L(\mathbb C^{X_1})\to\mathcal L(\mathbb C^{X_2})$ be a linear map between spaces of complex matrices, with $X_1, X_2$ finite. Then $\Phi$ is trace preserving, i.e. $\mathrm{Tr}\,\Phi(\rho) = \mathrm{Tr}\,\rho$ for every matrix $\rho$, if and only if its CJ matrix satisfies
--
--   $$\mathrm{Tr}_{X_2}\, M^{X_1X_2} = \mathbb 1^{X_1}.$$
--
--   Here $J = M^{X_1X_2} = [\mathcal I\otimes\Phi(|\phi^+\rangle\langle\phi^+|)]^{T}$ is the Choi–Jamiołkowski (CJ) matrix of the linear map $\Phi: \mathcal L(\mathbb C^{X_1})\to\mathcal L(\mathbb C^{X_2})$, with $|\phi^+\rangle = \sum_j|jj\rangle$ unnormalized and ${}^T$ the full transpose (OCB p. 3). Entrywise, with indices ordered $X_1\times X_2$,
--
--   $$J_{(i,k),(j,l)} = \Phi\big(|j\rangle\langle i|\big)_{lk}.$$
--
--   The partial trace over the second factor is $(\mathrm{Tr}_{X_2}M)_{ij} = \sum_k M_{(i,k),(j,k)}$, so $(\mathrm{Tr}_{X_2}J)_{ij} = \mathrm{Tr}\,\Phi(|j\rangle\langle i|)$. This is the trace-preservation half of the CJ characterization of CPTP maps stated on p. 4 of OCB 2012.
-- source:
--   O. Oreshkov, F. Costa, C. Brukner, Quantum correlations with no causal order, Nat. Commun. 3, 1092 (2012), https://arxiv.org/abs/1105.4464v3, p. 4 ('a map M^A is CPTP if and only if its CJ operator satisfies M^{A1A2} >= 0 and Tr_{A2} M^{A1A2} = 1^{A1}'), trace-preservation half; CJ matrix defined on p. 3

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_OCB2012_defs
import Definitions.Def_OCB2012_cj

open Matrix
open scoped Kronecker ComplexOrder

namespace OCB2012

theorem isTracePreserving_iff_ptrace_cj {x1 x2 : Type*} [Fintype x1] [Fintype x2]
    [DecidableEq x1] [DecidableEq x2] (Φ : Matrix x1 x1 ℂ →ₗ[ℂ] Matrix x2 x2 ℂ) :
    IsTracePreserving Φ ↔ ptrace₂ (cjMatrix Φ) = 1 := by sorry

end OCB2012
