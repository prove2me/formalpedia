-- Prove2me | Theorems.Thm_GlobalTheory_NilpotentKernelSurjective_aeval_surjective_of_isNilpotent_ker
-- name    : GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:33:49.490412+00:00
-- url     : https://prove2.me/theorems/b86677c5-a797-4122-a770-c3af0ac45a7e
-- title:
--   Nilpotent Kernel Surjective: aeval surjective of is Nilpotent ker
-- statement:
--   The Nilpotent Kernel Surjective construction uses the aeval surjective of is Nilpotent ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AevalSurjectiveOfIsNilpotentKer.lean#L48-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AevalSurjectiveOfIsNilpotentKer.lean#L48-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AevalSurjectiveOfIsNilpotentKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.NilpotentKernelSurjective

theorem GlobalTheory.NilpotentKernelSurjective.aeval_surjective_of_isNilpotent_ker :
    ∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : CommRing A]
      [inst_2 : Algebra R A] (ε : A →ₐ[R] R), IsNilpotent (RingHom.ker ε) →
      ∀ {d : ℕ} (x : Fin d → A), (∀ (i : Fin d), x i ∈ RingHom.ker ε) →
      (∀ y ∈ RingHom.ker ε, ∃ (l : Fin d → R),
        y - ∑ i : Fin d, l i • x i ∈ RingHom.ker ε ^ (2 : ℕ)) →
      Function.Surjective (⇑(MvPolynomial.aeval x) : MvPolynomial (Fin d) R → A) := by sorry
