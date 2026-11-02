-- Prove2me | Theorems.Thm_NishtAbel2024_lemma3_encoding_polarities
-- name    : NishtAbel2024.lemma3_encoding_polarities
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T23:43:37.06591+00:00
-- url     : https://prove2.me/theorems/aeb1fcda-324c-46cd-8e8c-3724c712d0ed
-- title:
--   Polarities of generated size annotations (Lemma 3, existing model)
-- statement:
--   Let polarized signature encoding with target polarity negative and initial polarity positive transform a type $A$ into $A'$ and generate size declarations $\Psi$, in a context $\Delta$. For each generated size name $i$, write $M_i^-$ for the existence of a negative inductive-fixpoint occurrence of $i$ in $A'$, and $N_i^+$ for the existence of a positive coinductive-fixpoint occurrence. Occurrences are judged in $\Delta$ extended by $\Psi$. Then
--
--   $$
--   \forall i\in\operatorname{dom}(\Psi),\qquad
--   (M_i^-\land\neg N_i^+)\;\lor\;(N_i^+\land\neg M_i^-).
--   $$
--
--   This classifies the generated size annotations by the specified inductive or coinductive occurrence and excludes the opposing case.
--
--   **Formalization Note** This is exactly the second conjunct of the existing bundled Theorems 7–9 and Lemmas 3–5 statement. It adds no context uniqueness, kinding, or freshness premises. The occurrence predicates assert existence of a derivation; this is not an all-occurrences uniform-polarity theorem. The published encoding relation includes extra target-kinding and disjointness premises relative to the printed presentation; source encoding completeness and global freshness remain separate obligations. This result does not establish Lemmas 4–5 or semantic soundness.
-- source:
--   Kanstantsin Nisht, Type-Based Termination Checking in Agda, 2024, Section 6.1, Lemma 3, printed p.43, https://knisht.github.io/agda/msc.pdf; exact second formal conjunct of Prove2Me theorem 60c982ad-4712-4445-8689-70bbff93fcd9.

import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024

theorem lemma3_encoding_polarities :
    (∀ (Δ : KindingCtx) (A A' : TypeExpr) (Ψ : SizeCtx),
      EncodeType .neg .pos Δ A Ψ A' →
      ∀ i ∈ Ψ.dom,
        (SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A' ∧
          ¬ SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A') ∨
        (SizeOccursFixPol (Δ.extSizes Ψ) .nu i .pos A' ∧
          ¬ SizeOccursFixPol (Δ.extSizes Ψ) .mu i .neg A')) := by sorry

end NishtAbel2024
