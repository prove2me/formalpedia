-- Prove2me | Theorems.Thm_LaarakkerOttenVanDenBerg2026_lemmas_15_17_and_prop_31
-- name    : LaarakkerOttenVanDenBerg2026.lemmas_15_17_and_prop_31
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T16:10:44.214926+00:00
-- url     : https://prove2.me/theorems/a9f67ad1-7c32-408e-b102-d25fa1b86301
-- title:
--   Lemma 15, Proposition 16/36, Proposition 31, and Lemma 17/37: Realisability Model Foundations
-- statement:
--   **Lemma 15 (p. 14), Proposition 31 (p. 30), Proposition 16/36 (pp. 15, 33), and Lemma 17/37 (pp. 16, 33–34)**:
--   1. **Lemma 15**: The functors $\iota : \mathsf{PER} \to \mathsf{Mod}$ (`iotaMod`) and $\mathcal{E} : \mathsf{Mod} \to \mathsf{PER}$ (`modToPER`) establish an equivalence between $\mathsf{PER}$ and small modest sets.
--   2. **Proposition 31**: In the CwF of assemblies, if $B \in \mathsf{Ty}(\Gamma.A)$ is modest, then the dependent product $\Pi(A, B)$ (`semPi`) is modest for any (possibly large) $A \in \mathsf{Ty}(\Gamma)$.
--   3. **Proposition 16 / 36**: Every partial combinatory algebra $(\mathcal{A}, \cdot)$ admits a fixpoint combinator $\mathsf{fix} \in \mathcal{A}$ (`IsPCAFixpoint`).
--   4. **Lemma 17 / 37**: The modest quotient functor $\mathsf{M} : \mathsf{Asm} \to \mathsf{Mod}$ (`modestQuotient`) is left adjoint to the inclusion $I : \mathsf{Mod} \to \mathsf{Asm}$.
-- source:
--   Bastiaan Laarakker, Daniël Otten, and Benno van den Berg, 'Constructing (Co)inductive Types via Large Sizes', FSCD 2026 (arXiv:2602.18921), Section 4 & Appendix C, Lemma 15, Proposition 16/36, Proposition 31, Lemma 17/37 (pp. 14–16, 30, 33–34)

import Definitions.Def_LaarakkerOttenVanDenBerg2026_Model

namespace LaarakkerOttenVanDenBerg2026

universe u

theorem lemmas_15_17_and_prop_31
    (P : NatPCA) :
    (∀ (R : PER) (m n : ℕ),
      (modToPER P.toPCA (iotaMod P.toPCA R)).rel m n ↔ R.rel m n) ∧
    (∀ (X : ModSet.{0} P.toPCA),
      ∃ (f : ModHom P.toPCA X (iotaMod P.toPCA (modToPER P.toPCA X)))
        (g : ModHom P.toPCA (iotaMod P.toPCA (modToPER P.toPCA X)) X),
        (∀ x, g.toFun (f.toFun x) = x) ∧ (∀ c, f.toFun (g.toFun c) = c)) ∧
    (∀ (Γ : SemCtx.{u} P.toPCA) (A : SemTy.{u} P.toPCA Γ)
      (B : SemTy.{u} P.toPCA (ctxExt P.toPCA Γ A)),
      IsModestTy P.toPCA (ctxExt P.toPCA Γ A) B →
        IsModestTy P.toPCA Γ (semPi P.toPCA Γ A B)) ∧
    (∀ {α : Type u} (Q : PCA α),
      ∃ (fixComb : α), IsPCAFixpoint Q fixComb) ∧
    (∀ (X : Asm.{u} P.toPCA) (Y : ModSet.{u} P.toPCA)
      (g : AsmHom P.toPCA X (modInclusionObj P.toPCA Y)),
      ∃! (f : ModHom P.toPCA (modestQuotient P.toPCA X) Y),
        asmHomComp P f (modestQuotientUnit P.toPCA X) = g) := by
  sorry

end LaarakkerOttenVanDenBerg2026
