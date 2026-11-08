-- Prove2me | Theorems.Thm_Grodin2026_lemma_5_1_and_theorem_5_7_giralf_and_aara_types
-- name    : Grodin2026.lemma_5_1_and_theorem_5_7_giralf_and_aara_types
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:18:52.230736+00:00
-- url     : https://prove2.me/theorems/f50dd157-8742-4a57-afaf-7c01fd87a574
-- title:
--   Lemma 5.1, Examples 5.2 & 5.3, and Theorem 5.7: Giralf Paramorphism, Insertion Sort, and Equivalence of Calf and AARA Types
-- statement:
--   Establishes the debit-and-lazy-product paramorphism state pairing in Giralf (Lemma 5.1), verifies the Giralf judgments for `insert` ($l : \mathsf{CList}^{1+p}_1(F\mathbb{N}) \vdash^p \mathsf{insert}\,x\,l : \mathsf{CList}^p_1(F\mathbb{N})$, Example 5.2) and `isort` ($l : \mathsf{CList}^{(0, 1)}_2(F\mathbb{N}) \vdash^0 \mathsf{isort}\,l : \mathsf{CList}^0_1(F\mathbb{N})$, Example 5.3), proves that the shifting-index inductive family `CList2Ind` stores $|t.\mathsf{toList}| \cdot p_1 + \binom{|t.\mathsf{toList}|}{2} \cdot p_2$ credits, and proves Theorem 5.7: for every positive AARA type $A$, `interpAARAType A` is equivalent to $\mathsf{Potential}(\Phi_A : \llbracket A \rrbracket \to \mathbb{N})$.
-- source:
--   Harrison Grodin, Ethan Chu, Runming Li, Jan Hoffmann, and Robert Harper, 'Potential Functions as Types: A Synthetic Modal Formulation of Amortized Cost', arXiv:2607.08547v2, 2026. Sections 5.1-5.2, Lemma 5.1, Examples 5.2-5.3, Theorem 5.7, pp. 18-20.

import Definitions.Def_Grodin2026_Giralf

namespace Grodin2026

/-- **Lemma 5.1, Example 5.2, Example 5.3, and Theorem 5.7 (§§5.1–5.2):**
1. **Derivable Credit-Aware Paramorphism Step Pairing (Lemma 5.1):**
   Given $q_1 + q_2 \le q$, a debit-guarded recursive branch
   $e_{\mathrm{rec}} : \mathsf{GiralfSemJudgment}\,\Delta\,B\,(q_1 + q_2)$ (which wraps via
   `giralfGet` into $\triangleleft^{q_2} B$ at credit level $q_1$), and a sublist branch
   $e_{\mathrm{sub}} : \mathsf{GiralfSemJudgment}\,\Delta\,(\mathsf{CList1Comp}\,p\,X)\,q_1$,
   pairing via `giralfPair` produces the lazy paramorphism state
   $\Delta \vdash^{q_1} (\mathsf{get}\langle q_2 \rangle(e_{\mathrm{rec}}), e_{\mathrm{sub}}) :
   \triangleleft^{q_2} B \times \mathsf{CList}^p_1(FX)$ from which either `giralfPay (giralfProj1 ...)`
   recovers $B$ at credit level $q$ or `giralfProj2` recovers $\mathsf{CList}^p_1(FX)$ at credit
   level $q_1$.
2. **Giralf `insert` via Paramorphism (Example 5.2):**
   For all $p, x : \mathbb{N}$ and $l : \mathsf{List}\,\mathbb{N}$,
   `(insertCostTop x l).2 = insertPure x l`,
   `(insertCostTop x l).2.length = l.length + 1`,
   `(insertCostTop x l).1 + (insertCostTop x l).2.length * p ≤ l.length * (1 + p) + p`, and
   `insertTopHom x` and `insertAbsHom x` form a valid Giralf judgment
   $l : \mathsf{CList}^{1 + p}_1(F\mathbb{N}) \vdash^p \mathsf{insert}\,x\,l : \mathsf{CList}^p_1(F\mathbb{N})$.
3. **Giralf `isort` via Indexed Quadratic-Credit Recursion (Example 5.3):**
   `isortTopHom` and `isortAbsHom` form a valid Giralf judgment
   $l : \mathsf{CList}^{(0, 1)}_2(F\mathbb{N}) \vdash^0 \mathsf{isort}\,l : \mathsf{CList}^0_1(F\mathbb{N})$.
4. **Equivalence of Calf AARA Types and Potential Types (Theorem 5.7):**
   - For every inductive quadratic-credit list $t : \mathsf{CList2Ind}\,\alpha\,p_1\,p_2$,
     its inductively-shifted credits equal the closed-form polynomial formula
     $|t.\mathsf{toList}| \cdot p_1 + \binom{|t.\mathsf{toList}|}{2} \cdot p_2$;
   - For every positive AARA type $A : \mathsf{AARAType}$, its Calf computation type interpretation
     `interpAARAType A` is equivalent (`CompEquiv`) to
     $\mathsf{Potential}(\Phi_A : \llbracket A \rrbracket \to \mathbb{N})$. -/
theorem lemma_5_1_and_theorem_5_7_giralf_and_aara_types :
    (∀ {Delta B : CompType} {X : Type} {p q q₁ q₂ : Nat} (hq : q₂ + q₁ ≤ q)
       (e_rec : GiralfSemJudgment Delta B (q₂ + q₁))
       (e_sub : GiralfSemJudgment Delta (CList1Comp p X) q₁),
      ∃ paraState : GiralfSemJudgment Delta (ProdComp (DebitComp q₂ B) (CList1Comp p X)) q₁,
        (giralfPay hq (giralfProj1 paraState)).hom_top = e_rec.hom_top ∧
        (giralfProj2 paraState).hom_top = e_sub.hom_top) ∧
    (∀ (p x : Nat),
      (∀ l : List Nat,
        (insertCostTop x l).2 = insertPure x l ∧
        (insertCostTop x l).2.length = l.length + 1 ∧
        (insertCostTop x l).1 + (insertCostTop x l).2.length * p ≤ l.length * (1 + p) + p) ∧
      ∃ ins : GiralfSemJudgment (CList1Comp (1 + p) Nat) (CList1Comp p Nat) p,
        ins.hom_top = insertTopHom x ∧ ins.hom_abs = insertAbsHom x) ∧
    (∃ srt : GiralfSemJudgment (CList2Comp 0 1 Nat) (CList1Comp 0 Nat) 0,
      srt.hom_top = isortTopHom ∧ srt.hom_abs = isortAbsHom) ∧
    (∀ {α : Type} {p₁ p₂ : Nat} (t : CList2Ind α p₁ p₂),
      t.credits = t.toList.length * p₁ + binom2 t.toList.length * p₂) ∧
    (∀ A : AARAType,
      Nonempty (CompEquiv (interpAARAType A)
        (PotentialType (aaraValues A) (aaraPotential A)))) := by
  sorry

end Grodin2026
