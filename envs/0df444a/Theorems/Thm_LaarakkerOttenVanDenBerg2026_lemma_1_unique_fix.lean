-- Prove2me | Theorems.Thm_LaarakkerOttenVanDenBerg2026_lemma_1_unique_fix
-- name    : LaarakkerOttenVanDenBerg2026.lemma_1_unique_fix
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T15:42:01.714915+00:00
-- url     : https://prove2.me/theorems/2c1573e3-6a03-414b-8279-6a7afb653180
-- title:
--   Lemma 1: Uniqueness of Size Fixpoints up to Contractibility
-- statement:
--   **Lemma 1 (Uniqueness of fixpoints, Section 2.2, p. 6)**: In any core size theory $T$, for every size-indexed type family $A : \mathsf{Size} \to \mathrm{Type}$ and every step function $f : \forall i,\,(\forall j < i.\,A(j)) \to A(i)$, the type of fixpoint solutions $\sum_{h : \forall i.\,A(i)} \forall i.\,(h\,i = f\,i\,(\lambda j < i.\,h\,j))$ (`T.FixpointSolution f`) is contractible (`IsContr`), with center $(\mathsf{fix}\,f, \mathsf{fix}^\beta\,f)$.
-- source:
--   Bastiaan Laarakker, Daniël Otten, and Benno van den Berg, 'Constructing (Co)inductive Types via Large Sizes', FSCD 2026 (arXiv:2602.18921), Section 2.2, Lemma 1 (p. 6)

import Definitions.Def_LaarakkerOttenVanDenBerg2026_TypeTheory

namespace LaarakkerOttenVanDenBerg2026

universe u v

theorem lemma_1_unique_fix (T : SizeCoreTheory.{u, v})
    (A : T.Size → Type (max u v))
    (f : (i : T.Size) → ((j : T.Size) → T.Lt j i → A j) → A i) :
    Nonempty (IsContr (T.FixpointSolution f)) ∧
      ∀ (sol : T.FixpointSolution f),
        sol = ⟨T.fix f, T.fix_beta f⟩ := by
  sorry

end LaarakkerOttenVanDenBerg2026
