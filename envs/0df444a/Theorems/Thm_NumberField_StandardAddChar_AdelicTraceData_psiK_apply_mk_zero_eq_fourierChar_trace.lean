-- Prove2me | Theorems.Thm_NumberField_StandardAddChar_AdelicTraceData_psiK_apply_mk_zero_eq_fourierChar_trace
-- name    : NumberField.StandardAddChar.AdelicTraceData.psiK_apply_mk_zero_eq_fourierChar_trace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/f4fd8143-1f3e-5756-84d1-872de5f1a47c
-- title:
--   Archimedean component of the standard adelic character
-- statement:
--   Let $F$ be a number field and let $T$ be an adelic trace datum for $F$, i.e. a pair of additive homomorphisms $\mathrm{Tr}_f \colon \mathbb{A}_F^{\mathrm{fin}} \to \mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ on finite adèle rings and $\mathrm{Tr}_\infty \colon F_\infty \to \mathbb{Q}_\infty$ on infinite adèle rings, both continuous, with $\mathrm{Tr}_\infty$ surjective, and both compatible with the principal embeddings in the sense that $\mathrm{Tr}_f(\iota q) = \iota(\mathrm{Tr}_{F/\mathbb{Q}} q)$ and $\mathrm{Tr}_\infty(\iota q) = \iota(\mathrm{Tr}_{F/\mathbb{Q}} q)$ for all $q \in F$. The associated character is $\psi_F = \psi_{\mathbb{Q}} \circ (\mathrm{Tr}_\infty \times \mathrm{Tr}_f)$, where $\psi_{\mathbb{Q}}$ is the additive character of $\mathbb{A}_{\mathbb{Q}} = \mathbb{Q}_\infty \times \mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ given by the product of the character `psiArch` evaluated at the infinite component and the character `psiFin` evaluated at the finite component. The assertion is that for every $x \in F_\infty$, the value of $\psi_F$ at the adèle $(x, 0)$ with vanishing finite part equals $e^{2\pi i t}$, viewed in $\mathbb{C}$, where $t = \mathrm{Tr}_{F_{\mathbb{R}}/\mathbb{R}}$ of the image of $x$ under the ring isomorphism from $F_\infty$ to the mixed space $\prod_{\text{real}} \mathbb{R} \times \prod_{\text{complex}} \mathbb{C}$ of $F$; here $e^{2\pi i t}$ is expressed through `Real.fourierChar`.
--
--   This identifies the archimedean part of the standard additive character $\psi_F$ of $\mathbb{A}_F$ built from a trace datum, in the normalisation $\psi_\infty(t) = e^{2\pi i t}$ transported to the Minkowski (mixed) space of $F$. It serves the construction of the standard global additive character used in the adelic Fourier analysis, and is cited by [`NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace`](thm.html#NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_StandardAddChar_AdelicTraceData_psiK_apply_mk_zero_eq_fourierChar_trace.lean

import Definitions.Def_NumberField_StandardGlobalAddChar
import Mathlib.Analysis.Fourier.FourierTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.StandardAddChar IsDedekindDomain

theorem NumberField.StandardAddChar.AdelicTraceData.psiK_apply_mk_zero_eq_fourierChar_trace
    (F : Type) [Field F] [NumberField F] (T : AdelicTraceData F) (x : InfiniteAdeleRing F) :
    T.psiK (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by sorry
