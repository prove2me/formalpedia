-- Prove2me | Theorems.Thm_NeutrinoDecoherence_relativeEntropy_nonneg
-- name    : NeutrinoDecoherence.relativeEntropy_nonneg
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T12:04:16.242989+00:00
-- url     : https://prove2.me/theorems/fc0df0ac-66a5-42f3-913f-2af8c8faf304
-- title:
--   Non-negativity of the relative entropy, eq. (2.43)
-- statement:
--   Let $\rho,\sigma$ be $n\times n$ density matrices with $\sigma$ positive definite, and let $S(\rho\|\sigma)=\operatorname{Tr}(\rho\ln\rho)-\operatorname{Tr}(\rho\ln\sigma)$. Then
--   $$S(\rho\|\sigma)\ge 0,$$
--   and $S(\rho\|\sigma)=0$ if and only if $\rho=\sigma$.
--
--   This inequality, together with the monotonicity (B.1) that the thesis cites from the literature, underlies the entropy-increase argument of Appendix B.1.
--
--   **Formalization Note** The thesis states (2.43) "for all $\rho$ and $\sigma$". When $\sigma$ is singular and $\rho$ has support outside that of $\sigma$ the relative entropy is $+\infty$; since the Lean version is real-valued, it assumes $\sigma$ positive definite so that $\ln\sigma$ is well defined.
-- source:
--   G. F. S. Alves, *Decoherence in Neutrino Oscillations in the IceCube Experiment* (Descoerência em Oscilações de Neutrinos no Experimento IceCube), MSc dissertation, Instituto de Física, Universidade de São Paulo, 2020; supervisor R. Zukanovich Funchal; Section 2.2.3, p. 50, eqs. (2.42)–(2.43).

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs
open Matrix Complex
open scoped ComplexOrder

namespace NeutrinoDecoherence
theorem relativeEntropy_nonneg {n : Type*} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ)
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) (hσpos : σ.PosDef) :
    0 ≤ relativeEntropy ρ σ ∧ (relativeEntropy ρ σ = 0 ↔ ρ = σ) := by sorry
end NeutrinoDecoherence
