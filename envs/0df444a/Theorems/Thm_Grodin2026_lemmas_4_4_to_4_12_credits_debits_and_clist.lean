-- Prove2me | Theorems.Thm_Grodin2026_lemmas_4_4_to_4_12_credits_debits_and_clist
-- name    : Grodin2026.lemmas_4_4_to_4_12_credits_debits_and_clist
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:18:39.408777+00:00
-- url     : https://prove2.me/theorems/92ea2887-ab18-4050-9f6d-f36207d853f4
-- title:
--   Lemmas 4.4, 4.6, 4.8, 4.10, 4.12, Corollaries 4.14 & 4.19, and Example 4.15: Credits, Debits, and Credit-Carrying Lists
-- statement:
--   Proves that credits are ghost data ($\bullet(\triangleright^c A) = \bullet A$ and $\bigcirc(\triangleright^c A) = \bigcirc A$, Lemma 4.4), the monoidal laws $\triangleright^0 A = A$ and $\triangleright^{c_1 + c_2} A = \triangleright^{c_1}(\triangleright^{c_2} A)$ (Lemma 4.6), the companion identity $\mathsf{spend}\langle c \rangle \circ \mathsf{save}\langle c \rangle = \mathsf{charge}_A\langle c \rangle$ (Lemma 4.8), the equivalence $\mathsf{Potential}(\Phi) \simeq (x : X) \ltimes \triangleright^{\Phi(x)} \top$ connecting the physicist's and banker's views (Lemma 4.10), the credit-debit hom-set adjunction $\mathsf{LaxCompHom}(\triangleright^c A, B) \simeq \mathsf{CompHom}(A, \triangleleft^c B)$ (Lemma 4.12), abstract-phase erasure for $\mathsf{CList}^c_1(FX)$ and $\mathsf{CList}^{(c_1, c_2)}_2(FX)$ (Corollaries 4.14 & 4.19), and the zero-abstract-cost homomorphism for pre-paid list reversal (Example 4.15).
-- source:
--   Harrison Grodin, Ethan Chu, Runming Li, Jan Hoffmann, and Robert Harper, 'Potential Functions as Types: A Synthetic Modal Formulation of Amortized Cost', arXiv:2607.08547v2, 2026. Section 4, Lemmas 4.4, 4.6, 4.8, 4.10, 4.12, Corollaries 4.14 & 4.19, Example 4.15, pp. 14-16.

import Definitions.Def_Grodin2026_Banker

namespace Grodin2026

/-- **Lemma 4.4, Lemma 4.6, Lemma 4.8, Lemma 4.10, Lemma 4.12, Corollaries 4.14 & 4.19, and Example 4.15 (§4):**
1. **Credits Are Ghost Data (Lemma 4.4):** For all $c : \mathbb{N}$ and $A : \mathcal{C}$,
   $\bullet(\triangleright^c A) = \bullet A$ and $\bigcirc(\triangleright^c A) = \bigcirc A$.
2. **Monoidal Laws of the Credit Operator (Lemma 4.6):** For all $A : \mathcal{C}$ and
   $c_1, c_2 : \mathbb{N}$, $\triangleright^0 A = A$ and
   $\triangleright^{c_1 + c_2} A = \triangleright^{c_1}(\triangleright^{c_2} A)$.
3. **Save–Spend Companion Identity (Lemma 4.8):** For all $c : \mathbb{N}$ and $A : \mathcal{C}$,
   $\mathsf{spend}\langle c \rangle \circ \mathsf{save}\langle c \rangle = \mathsf{charge}_A\langle c \rangle$.
4. **Physicist–Banker Equivalence (Lemma 4.10):** For any value type $X$ and potential function
   $\Phi : X \to \mathbb{N}$, $\mathsf{Potential}(\Phi : X \to \mathbb{N}) \simeq (x : X) \ltimes \triangleright^{\Phi(x)} \top$.
5. **Credit–Debit Adjunction $\triangleright^c \dashv \triangleleft^c$ (Lemma 4.12):** For all
   $c : \mathbb{N}$ and $A, B : \mathcal{C}$, there is a canonical equivalence of hom-types
   $\mathsf{LaxCompHom}(\triangleright^c A, B) \simeq \mathsf{CompHom}(A, \triangleleft^c B)$
   mediated by the loan unit $\eta_c : A \multimap \triangleleft^c \triangleright^c A$ and loan
   counit $\varepsilon_c : \triangleright^c \triangleleft^c B \mathrel{\multimap\!\!\!\!+} B$.
6. **Credit-Carrying Lists and Linear-Time Pre-Paid `reverse` (Corollaries 4.14 & 4.19, Example 4.15):**
   - In the abstract phase ($\bigcirc$), both linear-credit lists $\mathsf{CList}^c_1(FX)$ and
     quadratic-credit lists $\mathsf{CList}^{(c_1, c_2)}_2(FX)$ erase their credit annotations to
     $\bigcirc(F(\mathsf{List}\,X))$;
   - For every list $l$ and accumulator $acc$, `revAppendTop l acc = (l.length, l.reverseAux acc)`,
     and `reverseCList1Top` and `reverseCList1Abs` assemble into a strict computation homomorphism
     $\mathsf{reverse} : \mathsf{CList}^1_1(FX) \multimap F(\mathsf{List}\,X)$ with zero abstract cost. -/
theorem lemmas_4_4_to_4_12_credits_debits_and_clist :
    (∀ (c : Nat) (A : CompType),
      ClosedComp (CreditComp c A) = ClosedComp A ∧
      OpenComp (CreditComp c A) = OpenComp A) ∧
    (∀ (A : CompType),
      CreditComp 0 A = A ∧
      (∀ c₁ c₂ : Nat, CreditComp (c₁ + c₂) A = CreditComp c₁ (CreditComp c₂ A))) ∧
    (∀ (c : Nat) (A : CompType),
      (spendComp c A).comp (saveComp c A) = chargeCompHom A c) ∧
    (∀ (X : Type) (Phi : X → Nat),
      Nonempty (CompEquiv (PotentialType X Phi) (BankerPotentialComp X Phi))) ∧
    (∀ (c : Nat) (A B : CompType),
      Nonempty (LaxCompHom (CreditComp c A) B ≃ CompHom A (DebitComp c B))) ∧
    (∀ (X : Type) (c c₁ c₂ : Nat),
      OpenComp (CList1Comp c X) = OpenComp (FreeComp (List X)) ∧
      OpenComp (CList2Comp c₁ c₂ X) = OpenComp (FreeComp (List X)) ∧
      (∀ l acc : List X, revAppendTop l acc = (l.length, l.reverseAux acc)) ∧
      ∃ revHom : CompHom (CList1Comp 1 X) (FreeComp (List X)),
        revHom.hom_top = reverseCList1Top ∧ revHom.hom_abs = reverseCList1Abs) := by
  sorry

end Grodin2026
