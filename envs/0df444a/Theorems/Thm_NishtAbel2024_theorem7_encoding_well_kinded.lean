-- Prove2me | Theorems.Thm_NishtAbel2024_theorem7_encoding_well_kinded
-- name    : NishtAbel2024.theorem7_encoding_well_kinded
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T23:32:12.919198+00:00
-- url     : https://prove2.me/theorems/462c2f97-5c64-409c-bd59-fcede735f221
-- title:
--   Well-kindedness of signature encoding (Theorem 7, existing model)
-- statement:
--   Let $\Delta$ be a kinding context whose size declarations are well formed, let $A$ be an unannotated type of simple kind $*$, and let $\pi^*,\pi$ be polarities. If the published polarized encoding relation transforms $A$ into $A'$ while generating size declarations $\Psi$, then universally quantifying those generated sizes gives a well-kinded type:
--
--   $$
--   \Delta\vdash_{F_\omega} A\Leftarrow *
--   \quad\text{and}\quad
--   \pi;\Delta\vdash_{\mathrm{SCT}}^{\pi^*} A\Rightarrow\Psi;A'
--   \quad\Longrightarrow\quad
--   \Delta\vdash\forall\Psi.\,A'\Leftarrow *.
--   $$
--
--   This establishes the kinding part of signature encoding needed before pattern and spine elaboration.
--
--   **Formalization Note** This is exactly the first conjunct of the existing bundled Theorems 7–9 and Lemmas 3–5 statement, with no added assumptions or restricted syntax. The published encoding relation has extra target-kinding certificates and disjointness premises relative to the printed rules; completeness for all source encodings and global freshness conventions is a separate obligation. The result concerns the existing kinding and bounded-binder rules and does not establish the polarity-classification lemmas or semantic soundness.
-- source:
--   Kanstantsin Nisht, Type-Based Termination Checking in Agda, 2024, Section 6.1, Theorem 7, printed p.43, https://knisht.github.io/agda/msc.pdf; exact first formal conjunct of Prove2Me theorem 60c982ad-4712-4445-8689-70bbff93fcd9.

import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024

theorem theorem7_encoding_well_kinded :
    (∀ (πstar π : Polarity) (Δ : KindingCtx) (A A' : TypeExpr) (Ψ : SizeCtx),
      SizeCtxWf Δ.sizes →
      FwKindCheck Δ A .star →
      EncodeType πstar π Δ A Ψ A' →
      KindCheck Δ (TypeExpr.forallSizes Ψ A') .star) := by
  sorry

end NishtAbel2024
