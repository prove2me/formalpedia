-- Prove2me | Theorems.Thm_HoneycombCodes_lemma_D_7
-- name    : HoneycombCodes.lemma_D_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:29:30.537576+00:00
-- url     : https://prove2.me/theorems/3e8ce2ca-6209-4082-b34b-df4bd630074d
-- title:
--   Lemma D.7 — the unmasked endpoint $A=1$ is MQC
-- statement:
--   Every closed 2MQC-feasible point $(u,v)\in F_\delta$ with $A_\delta(u,v)=1$ satisfies
--
--   $$
--   \Psi_\delta(u,v)\ge R_{MQC}(\delta).
--   $$
--
--   The infimum over the $A=1$ branch is exactly $R_{MQC}(\delta)$.
--
--   **Formalization Note** The infimum over the $A=1$ branch is taken over the strictly feasible pairs of (124) with $A_\delta=1$, as in the proof.
--
--   Differences from the source:
--
--   - reading: the standing range of δ in Appendix D → hypotheses 0 < δ < 1/2; reason: App. D works throughout at 0 < δ < 1/2
--   - reading: 'the infimum over the A = 1 branch' → sInf of Ψ_δ over the strictly feasible pairs of (124) with A_δ(u, v) = 1; reason: the proof (p.65) computes 'the strict-feasibility infimum on the A = 1 branch'
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), App. D.5, Lemma D.7, p.64 (PDF 66)

import Mathlib
import Definitions.Def_HoneycombCodes_R2MQC
import Definitions.Def_HoneycombCodes_RMQC

set_option autoImplicit false

namespace HoneycombCodes

/-- **Lemma D.7**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), App. D.5, p.64 (PDF 66). Every closed 2MQC-feasible point with
`A_δ(u, v) = 1` satisfies `Ψ_δ(u, v) ≥ R_MQC(δ)`. The infimum over the `A = 1` branch is exactly
`R_MQC(δ)`.

**Formalization Note.** Stated for `0 < δ < 1/2`. "Closed 2MQC-feasible" is membership in `F_δ`
(126). "The infimum over the A = 1 branch" is the real `sInf` of `Ψ_δ` over the strictly feasible
pairs of (124) with `A_δ = 1` (the strict-feasibility infimum of the proof, p.65). -/
theorem lemma_D_7 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    (∀ u v : ℝ, (u, v) ∈ Fset δ → Adelta δ u v = 1 → RMQC δ ≤ PsiDelta δ u v) ∧
    sInf {r : ℝ | ∃ u v : ℝ, StrictFeasible2MQC δ u v ∧ Adelta δ u v = 1 ∧
      r = PsiDelta δ u v} = RMQC δ := by sorry

end HoneycombCodes
