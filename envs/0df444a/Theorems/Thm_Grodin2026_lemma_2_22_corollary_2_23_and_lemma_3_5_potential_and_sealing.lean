-- Prove2me | Theorems.Thm_Grodin2026_lemma_2_22_corollary_2_23_and_lemma_3_5_potential_and_sealing
-- name    : Grodin2026.lemma_2_22_corollary_2_23_and_lemma_3_5_potential_and_sealing
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T17:18:25.405825+00:00
-- url     : https://prove2.me/theorems/cdb0c821-771a-4628-9cc6-27a8d25ee372
-- title:
--   Example 2.20, Lemma 2.22, Corollary 2.23, Example 3.3, and Lemma 3.5: Potential Types, Amortized Interfaces, and Sealing
-- statement:
--   Verifies the conservation equation $0 + \Phi(l_1, n :: l_2) = \Phi(l_1, l_2) + 1$ and the $\mathsf{abs}$-phase amortized specification for ephemeral batched queues (Examples 2.20 & 3.3), proves the bidirectional conservation characterization $c_\top(x) + \Phi_Y(f(x)) = \Phi_X(x) + c_{\mathsf{abs}}(x)$ for homomorphisms between $\mathsf{Potential}$ types (Lemma 2.22), establishes one-sided lifting into and out of $\mathsf{Abstraction}(\beta)$ (Corollary 2.23), and proves the Kleisli bijection $(A \multimap \mathsf{S}B) \simeq (A \mathrel{\multimap\!\!\!\!+} B)$, abstract-phase erasure $\bigcirc(\mathsf{S}A) = \bigcirc A$ (Lemma 3.5), and the lax conservation characterization $c_\top(x) + \Phi_Y(f(x)) \le \Phi_X(x) + c_{\mathsf{abs}}(x)$ (§3.2).
-- source:
--   Harrison Grodin, Ethan Chu, Runming Li, Jan Hoffmann, and Robert Harper, 'Potential Functions as Types: A Synthetic Modal Formulation of Amortized Cost', arXiv:2607.08547v2, 2026. Sections 2.3 & 3.1-3.2, Example 2.20, Lemma 2.22, Corollary 2.23, Example 3.3, Lemma 3.5, pp. 10-13.

import Definitions.Def_Grodin2026_Physicist

namespace Grodin2026

/-- **Example 2.20, Lemma 2.22, Corollary 2.23, Example 3.3, and Lemma 3.5 (§§2.3–3.2):**
1. **Batched Queue Conservation & Amortized Interface (Example 2.20 & Example 3.3):**
   For any element type $\alpha$, concrete queue $(l_1, l_2)$, and element $n : \alpha$,
   $0 + \Phi(l_1, n :: l_2) = \Phi(l_1, l_2) + 1$, and there is a phased queue implementation
   $Q : \mathsf{PhasedPreQueue}\,\alpha$ over `BatchedQueueComp α` whose concrete enqueue is
   `enqueueCompTop` and whose abstract-phase view `Q.absView` is definitionally equal to the
   amortized queue specification `AmortizedQueueModel α`.
2. **Strict Conservation of Potential Characterization (Lemma 2.22):**
   Given $f : X \to Y$, true cost $c_\top : X \to \mathbb{N}$, and amortized cost
   $c_{\mathsf{abs}} : X \to \mathbb{N}$, there exists a strict computation homomorphism
   $g : \mathsf{Potential}(\Phi_X) \multimap \mathsf{Potential}(\Phi_Y)$ with
   $g_\top(\mathsf{ret}\,x) = (c_\top(x), f(x))$ and
   $g_{\mathsf{abs}}(\mathsf{ret}\,x) = (c_{\mathsf{abs}}(x), f(x))$ if and only if
   $c_\top(x) + \Phi_Y(f(x)) = \Phi_X(x) + c_{\mathsf{abs}}(x)$ for all $x : X$.
3. **One-Sided Lifting into/out of $\mathsf{Abstraction}$ (Corollary 2.23):**
   For $B = \mathsf{Abstraction}(\beta : B_\top \multimap B_{\mathsf{abs}})$ and any single-world
   cost algebra $A$, every $f_\top : A \multimap B_\top$ lifts to a computation homomorphism
   $\mathsf{ConstComp}\,A \multimap B$ with abstract component $\beta \circ f_\top$, and every
   $g_{\mathsf{abs}} : B_{\mathsf{abs}} \multimap A$ lifts to a computation homomorphism
   $B \multimap \mathsf{ConstComp}\,A$ with concrete component $g_{\mathsf{abs}} \circ \beta$.
4. **Sealing Monad $\mathsf{S}$, Kleisli Lax Homomorphisms, and Lax Conservation (§3.2 & Lemma 3.5):**
   - For all $A, B : \mathcal{C}$, Kleisli homomorphisms $A \multimap \mathsf{S}B$ are in canonical
     bijection (`Equiv`) with lax homomorphisms $A \mathrel{\multimap\!\!\!\!+} B$;
   - In the abstract phase ($\bigcirc$), sealing is erased: $\bigcirc(\mathsf{S}A) = \bigcirc A$
     (Lemma 3.5);
   - A lax homomorphism $g : \mathsf{Potential}(\Phi_X) \mathrel{\multimap\!\!\!\!+} \mathsf{Potential}(\Phi_Y)$
     with $g_\top(\mathsf{ret}\,x) = (c_\top(x), f(x))$ and
     $g_{\mathsf{abs}}(\mathsf{ret}\,x) = (c_{\mathsf{abs}}(x), f(x))$ exists if and only if the
     lax conservation inequality $c_\top(x) + \Phi_Y(f(x)) \le \Phi_X(x) + c_{\mathsf{abs}}(x)$
     holds for all $x : X$. -/
theorem lemma_2_22_corollary_2_23_and_lemma_3_5_potential_and_sealing :
    (∀ (α : Type),
      (∀ (q : BatchedQueueRep α) (n : α), 0 + queuePhi (enqueueValTop n q) = queuePhi q + 1) ∧
      ∃ enq : α → CompHom (BatchedQueueComp α) (BatchedQueueComp α),
        (∀ n : α, (enq n).hom_top = enqueueCompTop n) ∧
        ({ comp := BatchedQueueComp α
           empty_top := retFree ([], [])
           empty_abs := retFree []
           empty_comm := rfl
           enqueue := enq } : PhasedPreQueue α).absView = AmortizedQueueModel α) ∧
    (∀ {X Y : Type} (Phi_X : X → Nat) (Phi_Y : Y → Nat) (f : X → Y) (c_top c_abs : X → Nat),
      (∃ g : CompHom (PotentialType X Phi_X) (PotentialType Y Phi_Y),
        (∀ x : X, g.hom_top.fn (retFree x) = (c_top x, f x)) ∧
        (∀ x : X, g.hom_abs.fn (retFree x) = (c_abs x, f x))) ↔
      (∀ x : X, c_top x + Phi_Y (f x) = Phi_X x + c_abs x)) ∧
    (∀ (A B_top B_abs : CostAlg) (beta : CostHom B_top B_abs),
      (∀ f_top : CostHom A B_top,
        ∃ f : CompHom (ConstComp A) (AbstractionComp B_top B_abs beta),
          f.hom_top = f_top ∧ f.hom_abs = beta.comp f_top) ∧
      (∀ g_abs : CostHom B_abs A,
        ∃ g : CompHom (AbstractionComp B_top B_abs beta) (ConstComp A),
          g.hom_top = g_abs.comp beta ∧ g.hom_abs = g_abs)) ∧
    (∀ A B : CompType,
      Nonempty (CompHom A (SealComp B) ≃ LaxCompHom A B) ∧
      OpenComp (SealComp A) = OpenComp A) ∧
    (∀ {X Y : Type} (Phi_X : X → Nat) (Phi_Y : Y → Nat) (f : X → Y) (c_top c_abs : X → Nat),
      (∃ g : LaxCompHom (PotentialType X Phi_X) (PotentialType Y Phi_Y),
        (∀ x : X, g.hom_top.fn (retFree x) = (c_top x, f x)) ∧
        (∀ x : X, g.hom_abs.fn (retFree x) = (c_abs x, f x))) ↔
      (∀ x : X, c_top x + Phi_Y (f x) ≤ Phi_X x + c_abs x)) := by
  sorry

end Grodin2026
