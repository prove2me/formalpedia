-- Prove2me | Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
-- name    : NumberField.StandardAddChar.isGlobalAddChar_stdAddChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/18e6f789-efe9-58e1-b6e9-dce9b11c82c9
-- title:
--   The standard adelic character ψ_F is global
-- statement:
--   Let $F$ be a number field, i.e. a field $F$ (in the universe of types of sort `Type`) equipped with a `NumberField` structure, so that the adele ring $\mathbb{A}_F$ of $F$ over its ring of integers $\mathcal{O}_F$ is available as `AdeleRing (𝓞 F) F`. The character under consideration is `stdAddChar F`, namely the character `psiK` attached to the canonical trace datum `adelicTraceData F`; the latter is produced by `archTraceDataOf` from the trace homomorphism `traceFinHom F`, its compatibility with the algebra map $F \to \mathbb{A}_F$ and its continuity, and `psiK` is the composition of the standard additive character `psiQ` of the rational adeles with the adelic trace homomorphism of the datum. The assertion `IsGlobalAddChar F (stdAddChar F)` is the conjunction of three properties of this additive character $\psi_F : \mathbb{A}_F \to \mathbb{C}^{\times}$: it is principal-invariant, that is $\psi_F(\iota(\alpha)) = 1$ for every $\alpha \in F$, where $\iota$ denotes the algebra map of $F$ into $\mathbb{A}_F$; it is continuous; and it is not the trivial character.
--
--   This is the existence, for an arbitrary number field, of the standard additive character $\psi_F = \psi_{\mathbb{Q}} \circ \operatorname{Tr}_{\mathbb{A}}$ of $\mathbb{A}_F$ trivial on the principal adeles, the character underlying adelic Fourier analysis and Pontryagin duality for $\mathbb{A}_F/F$. It supplies a canonical witness for the hypothesis `IsGlobalAddChar` used throughout the treatment of Whittaker coefficients and class sums for automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar.lean

import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.StandardAddChar AutomorphicForm

theorem NumberField.StandardAddChar.isGlobalAddChar_stdAddChar
    (F : Type) [Field F] [NumberField F] :
    IsGlobalAddChar F (stdAddChar F) := by sorry
