-- Prove2me | Theorems.Thm_Grodin2026_theorem_5_8_soundness_of_aara_and_giralf_synthesis
-- name    : Grodin2026.theorem_5_8_soundness_of_aara_and_giralf_synthesis
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T17:19:21.244988+00:00
-- url     : https://prove2.me/theorems/7b5f3a8d-0bba-4aa6-83af-b7e6f6ca6ab3
-- title:
--   Theorem 5.8, Remark 5.5, and Example 5.18: Soundness of AARA and Certified Cost Inference for Calf Insertion Sort
-- statement:
--   Proves the Soundness Theorem of AARA (Theorem 5.8) from the Kripke semantics of Calf ($p + \Phi_A(v) \le \Phi_\Delta(\delta) + q$ whenever $e_\top(\mathsf{ret}\,\delta) = (p, v)$ and $e_{\mathsf{abs}}$ is cost-erased), proves that pre-paying via $e \circ \mathsf{save}\langle q \rangle$ preserves concrete execution while publicizing $q$ as the amortized cost in the abstract phase (Remark 5.5), constructs the resource-polymorphic cost inference certificate $\mathsf{CList}^{(p_1, p_2 + 1)}_2(F\mathbb{N}) \vdash^0 \underline{\mathsf{isort}} : \mathsf{CList}^{(p_1, p_2)}_2(F\mathbb{N})$ (Definition 5.9, Example 5.18), and derives the certified $\binom{|l|}{2}$ comparison bound for Calf insertion sort.
-- source:
--   Harrison Grodin, Ethan Chu, Runming Li, Jan Hoffmann, and Robert Harper, 'Potential Functions as Types: A Synthetic Modal Formulation of Amortized Cost', arXiv:2607.08547v2, 2026. Sections 5.2-5.3, Remark 5.5, Theorem 5.8, Definition 5.9, Example 5.18, pp. 19-24.

import Definitions.Def_Grodin2026_Giralf

namespace Grodin2026

/-- **Theorem 5.8, Remark 5.5, Definition 5.9, and Example 5.18 (§§5.2–5.3):**
1. **Soundness of AARA via Kripke Semantics of Calf (Theorem 5.8):**
   Let $\Delta, A : \mathsf{AARAType}$ be positive AARA types and let
   $e : \mathsf{GiralfSemJudgment}\,(\mathsf{PotentialType}\,\llbracket \Delta \rrbracket\,\Phi_\Delta)\,(\mathsf{PotentialType}\,\llbracket A \rrbracket\,\Phi_A)\,q$
   be a Giralf program whose abstract phase incurs zero cost (`IsZeroCostFreeHom e.hom_abs`).
   If evaluating $e_\top$ on environment $\delta : \llbracket \Delta \rrbracket$ (`retFree δ`)
   yields $(p, v) : \mathbb{N} \times \llbracket A \rrbracket$, then $v = (e_{\mathsf{abs}}(\mathsf{ret}\,\delta)).2$
   and the AARA conservation inequality holds:
   $$p + \Phi_A(v) \le \Phi_\Delta(\delta) + q.$$
2. **Pre-Payment Reframes Credit Context as Amortized Cost (Remark 5.5):**
   For any Giralf program $e : \mathsf{GiralfSemJudgment}\,(\mathsf{PotentialType}\,X\,\Phi_X)\,(\mathsf{PotentialType}\,Y\,\Phi_Y)\,q$
   with `IsZeroCostFreeHom e.hom_abs`, pre-paying via `prepayGiralf e = e.comp (saveComp q _).toLax`
   preserves the concrete program `(prepayGiralf e).hom_top = e.hom_top` while publicizing $q$ as
   the amortized cost in the abstract phase:
   $\forall x : X,\; ((\mathsf{prepayGiralf}\,e)_{\mathsf{abs}}(\mathsf{ret}\,x)).1 = q$.
3. **Resource-Polymorphic Cost Inference and Certified $\binom{|l|}{2}$ Bound for Calf Insertion Sort (Definition 5.9 & Example 5.18):**
   - For all $p_1, p_2 : \mathbb{N}$, `isortTopHom` and `isortAbsHom` inhabit the resource-polymorphic
     Giralf judgment
     $l : \mathsf{CList}^{(p_1, p_2 + 1)}_2(F\mathbb{N}) \vdash^0 \underline{\mathsf{isort}}\,l : \mathsf{CList}^{(p_1, p_2)}_2(F\mathbb{N})$
     and form a valid `CostInferenceCertificate isortTopHom isortAbsHom`;
   - Setting $p_1 = p_2 = 0$, for every input list $l : \mathsf{List}\,\mathbb{N}$,
     $(\mathsf{isortCostTop}\,l).2 = \mathsf{isortPure}\,l$ and
     $(\mathsf{isortCostTop}\,l).1 \le \binom{|l|}{2}$. -/
theorem theorem_5_8_soundness_of_aara_and_giralf_synthesis :
    (∀ (Delta A : AARAType) (q : Nat)
       (e : GiralfSemJudgment
         (PotentialType (aaraValues Delta) (aaraPotential Delta))
         (PotentialType (aaraValues A) (aaraPotential A)) q),
      IsZeroCostFreeHom e.hom_abs →
      ∀ (delta : aaraValues Delta) (p : Nat) (v : aaraValues A),
        e.hom_top.fn (retFree delta) = (p, v) →
        v = (e.hom_abs.fn (retFree delta)).2 ∧
        p + aaraPotential A v ≤ aaraPotential Delta delta + q) ∧
    (∀ {X Y : Type} (Phi_X : X → Nat) (Phi_Y : Y → Nat) (q : Nat)
       (e : GiralfSemJudgment (PotentialType X Phi_X) (PotentialType Y Phi_Y) q),
      IsZeroCostFreeHom e.hom_abs →
      (prepayGiralf e).hom_top = e.hom_top ∧
      ∀ x : X, ((prepayGiralf e).hom_abs.fn (retFree x)).1 = q) ∧
    (∀ p₁ p₂ : Nat,
      ∃ cert : CostInferenceCertificate isortTopHom isortAbsHom,
        cert.A_inf = CList2Comp p₁ (p₂ + 1) Nat ∧
        cert.B_inf = CList2Comp p₁ p₂ Nat ∧
        cert.q = 0) ∧
    (∀ l : List Nat,
      (isortCostTop l).2 = isortPure l ∧
      (isortCostTop l).1 ≤ binom2 l.length) := by
  sorry

end Grodin2026
