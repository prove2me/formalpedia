-- Prove2me | Theorems.Thm_Grodin2026_lemmas_5_10_5_15_and_5_16_cost_inference
-- name    : Grodin2026.lemmas_5_10_5_15_and_5_16_cost_inference
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:19:08.707532+00:00
-- url     : https://prove2.me/theorems/54746fc1-37bb-4fad-ac29-bedef41d4858
-- title:
--   Lemma 5.10, Corollary 5.11, Lemmas 5.15 & 5.16, and Examples 5.14 & 5.17: Concrete Erasure and Linear Algebra of Cost Inference
-- statement:
--   Proves concrete $\neg\mathsf{abs}$ erasure for both synthetic modalities and phased computation types (Lemma 5.10, Corollary 5.11), proves that cost-free annotations (`ValidSnocRecAnnotation 0`) are closed under $\oplus$ and $k \odot -$ (Lemma 5.15) and cost-aware annotations (`ValidSnocRecAnnotation stepCost`) are closed under $\oplus$ with cost-free annotations (Lemma 5.16), and verifies the three LP basis annotations $A_{\mathrm{ca}}, A_{\mathrm{cf1}}, A_{\mathrm{cf2}}$ and their symbolic linear combination $A_{\mathrm{ca}} \oplus (p_1 \odot A_{\mathrm{cf1}}) \oplus (p_2 \odot A_{\mathrm{cf2}})$ for $\underline{\mathsf{snoc'}}$ (Examples 5.14 & 5.17).
-- source:
--   Harrison Grodin, Ethan Chu, Runming Li, Jan Hoffmann, and Robert Harper, 'Potential Functions as Types: A Synthetic Modal Formulation of Amortized Cost', arXiv:2607.08547v2, 2026. Section 5.3, Lemma 5.10, Corollary 5.11, Example 5.14, Lemmas 5.15-5.16, Example 5.17, pp. 21-23.

import Definitions.Def_Grodin2026_Giralf

namespace Grodin2026

/-- **Lemma 5.10, Corollary 5.11, Example 5.14, Lemma 5.15, Lemma 5.16, and Example 5.17 (§5.3):**
1. **Synthetic and Phased $\neg\mathsf{abs}$ Erasure (Lemma 5.10 & Corollary 5.11):**
   - Under `¬ abs`, the synthetic abstract modality `OpenModal abs X` is contractible (`≃ PUnit`)
     and the synthetic concrete pushout `ClosedModal abs X` is equivalent to `X` (`≃ X`);
   - In the concrete ($\neg\mathsf{abs}$) world `.top`,
     $\mathsf{Abstraction}(\alpha : A_\top \multimap A_{\mathsf{abs}})_\top = A_\top$ (Lemma 5.10),
     $(\triangleright^p A)_\top = A_\top$ and $(\mathsf{spend}\langle c \rangle)_\top = \mathsf{charge}_{A_\top}\langle c \rangle$
     (Corollary 5.11(1)), and $(\mathsf{CList}^c_1(FX))_\top = (\mathsf{CList}^{(c_1, c_2)}_2(FX))_\top = F(\mathsf{List}\,X)$
     (Corollary 5.11(3)).
2. **Closure of Cost-Free Annotations under $\oplus$ and $k \odot -$ (Lemma 5.15):**
   If $A_1, A_2 : \mathsf{ListRecAnnotation}$ are valid cost-free annotations
   (`ValidSnocRecAnnotation 0`), then so are $A_1 \oplus A_2$ and $k \odot A_1$ for all $k : \mathbb{N}$.
3. **Closure of Cost-Aware Annotations under $\oplus$ with Cost-Free Annotations (Lemma 5.16):**
   If $A_1$ is a valid cost-aware annotation (`ValidSnocRecAnnotation stepCost A₁`) and $A_2$ is a
   valid cost-free annotation (`ValidSnocRecAnnotation 0 A₂`), then $A_1 \oplus A_2$ is a valid
   cost-aware annotation (`ValidSnocRecAnnotation stepCost (A₁ ⊕ A₂)`).
4. **Basis Inferences and Symbolic Combination for $\underline{\mathsf{snoc'}}$ (Examples 5.14 & 5.17):**
   - $A_{\mathrm{ca}}$ (`snocAnnCA`) is a valid cost-aware annotation (`stepCost = 1`) and
     $A_{\mathrm{cf1}}, A_{\mathrm{cf2}}$ (`snocAnnCF1`, `snocAnnCF2`) are valid cost-free annotations
     (`stepCost = 0`);
   - For all $p_1, p_2 : \mathbb{N}$, the symbolic linear combination
     $A_{\mathrm{ca}} \oplus (p_1 \odot A_{\mathrm{cf1}}) \oplus (p_2 \odot A_{\mathrm{cf2}})$
     (`snocSymbolicAnnotation p₁ p₂`) equals $\langle 1 + p_1 + p_2, p_2, 0, p_1, p_1, p_2 \rangle$
     and is a valid cost-aware annotation (`ValidSnocRecAnnotation 1`). -/
theorem lemmas_5_10_5_15_and_5_16_cost_inference :
    (∀ (abs : Prop) (X : Type),
      ¬ abs → Nonempty (OpenModal abs X ≃ PUnit) ∧ Nonempty (ClosedModal abs X ≃ X)) ∧
    (∀ (A_top A_abs : CostAlg) (alpha : CostHom A_top A_abs) (A : CompType)
       (X : Type) (p c c₁ c₂ : Nat),
      (AbstractionComp A_top A_abs alpha).top = A_top ∧
      (CreditComp p A).top = A.top ∧
      (spendComp c A).hom_top = chargeCostHom A.top c ∧
      (CList1Comp c X).top = FreeCostAlg (List X) ∧
      (CList2Comp c₁ c₂ X).top = FreeCostAlg (List X)) ∧
    (∀ (A₁ A₂ : ListRecAnnotation) (k : Nat),
      ValidSnocRecAnnotation 0 A₁ →
      ValidSnocRecAnnotation 0 A₂ →
      ValidSnocRecAnnotation 0 (ListRecAnnotation.add A₁ A₂) ∧
      ValidSnocRecAnnotation 0 (ListRecAnnotation.smul k A₁)) ∧
    (∀ (stepCost : Nat) (A₁ A₂ : ListRecAnnotation),
      ValidSnocRecAnnotation stepCost A₁ →
      ValidSnocRecAnnotation 0 A₂ →
      ValidSnocRecAnnotation stepCost (ListRecAnnotation.add A₁ A₂)) ∧
    (ValidSnocRecAnnotation 1 snocAnnCA ∧
     ValidSnocRecAnnotation 0 snocAnnCF1 ∧
     ValidSnocRecAnnotation 0 snocAnnCF2 ∧
     ∀ p₁ p₂ : Nat,
       snocSymbolicAnnotation p₁ p₂ = ⟨1 + p₁ + p₂, p₂, 0, p₁, p₁, p₂⟩ ∧
       ValidSnocRecAnnotation 1 (snocSymbolicAnnotation p₁ p₂)) := by
  sorry

end Grodin2026
