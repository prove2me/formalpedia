-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_Amplification_spatial_of_trace_iso
-- name    : OAI.FreeGroupFactorMain.Amplification.spatial_of_trace_iso
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T02:54:34.74822+00:00
-- url     : https://prove2.me/theorems/51cea6dd-6e03-4daa-a731-2099041f9890
-- title:
--   Trace-preserving isomorphisms of group algebras are spatial
-- statement:
--   Let $G,H$ be groups and $\Phi:L(G)\to L(H)$ a $*$-isomorphism with $\tau_H\circ\Phi=\tau_G$. There is a unitary $e:\ell^2(G)\to\ell^2(H)$ with $e\delta_e=\delta_e$ such that for every bounded operator $T$ on $\ell^2(G)$,
--
--   $$T\in L(G)\iff eTe^*\in L(H).$$
--
--   This is the standard-form implementation of a trace-preserving isomorphism by the GNS unitary; it is used to transfer amplification between isomorphic factors.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.Amplification.spatial_of_trace_iso`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/InterpolatedFactors/Spatial.lean#L65

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace FreeGroupFactorMain.Amplification

section

variable {G : Type u_1} {H : Type u_2} [Group G] [Group H]

theorem spatial_of_trace_iso (Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H)
    (ht : ∀ T, canonicalTrace (Φ T) = canonicalTrace T) :
    ∃ e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H,
      e deltaOne = deltaOne ∧
      ∀ T : GroupOperator G, T ∈ groupVonNeumann G ↔
        e.conjStarAlgEquiv T ∈ groupVonNeumann H := by
  sorry

end
end FreeGroupFactorMain.Amplification
end
end OAI
