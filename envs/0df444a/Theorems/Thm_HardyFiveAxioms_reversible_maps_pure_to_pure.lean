-- Prove2me | Theorems.Thm_HardyFiveAxioms_reversible_maps_pure_to_pure
-- name    : HardyFiveAxioms.reversible_maps_pure_to_pure
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T15:21:25.130733+00:00
-- url     : https://prove2.me/theorems/51a4d932-a340-4819-ba5d-fafd83587e59
-- title:
--   Reversible transformations send pure states to pure states
-- statement:
--   Let $S\subseteq\mathbb R^K$ be a set of states and let $Z$ be an invertible real $K\times K$ matrix such that both $Z$ and $Z^{-1}$ map $S$ into itself (a **reversible transformation**). If $p$ is a pure state of $S$, i.e. an extremal point of $S$ other than $0$, then
--
--   $$Zp\in S_{\rm pure}.$$
--
--   **Formalization Note** "$Z^{-1}$ exists and is in $\Gamma$" is encoded as invertibility of $Z$ together with $Z^{-1}S\subseteq S$. Pure states are as in the definition file `hardy2001_states`.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 15, Section 7, paragraph 'If a reversible transformation is applied to a pure state it must necessarily output a pure state'

import Mathlib
import Definitions.Def_hardy2001_states

namespace HardyFiveAxioms

open Matrix

/-- Hardy 2001, Section 7: a reversible transformation (an invertible matrix `Z` such that both
`Z` and `Z⁻¹` map the state space `S` into itself) sends pure states to pure states. -/
theorem reversible_maps_pure_to_pure {K : ℕ} (S : Set (Fin K → ℝ))
    (Z : Matrix (Fin K) (Fin K) ℝ) (hZ : IsUnit Z)
    (hZS : ∀ p ∈ S, Z *ᵥ p ∈ S) (hZinvS : ∀ p ∈ S, Z⁻¹ *ᵥ p ∈ S)
    (p : Fin K → ℝ) (hp : p ∈ pureStates S) :
    Z *ᵥ p ∈ pureStates S := by sorry

end HardyFiveAxioms
