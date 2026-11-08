-- Prove2me | Theorems.Thm_LaarakkerOttenVanDenBerg2026_theorem_23_coinductive_types
-- name    : LaarakkerOttenVanDenBerg2026.theorem_23_coinductive_types
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T16:10:27.605635+00:00
-- url     : https://prove2.me/theorems/c24ce0c9-ad8e-43d7-a9ef-25039ba8cdd1
-- title:
--   Proposition 5, Lemmas 19–20, Proposition 22, Theorem 23 & M-Type Corollary: Terminal Coalgebras via Universal Size Quantification
-- statement:
--   **Proposition 5 (p. 9), Lemmas 19–20 (p. 25), Proposition 22 (p. 26), Theorem 23 (p. 26), and Polynomial $M$-Type Corollary (p. 27)**:
--   In any `ParametricSizeTheory` $P$:
--   1. **Proposition 5**: The bounded universal modality $\Box$ (`boxMap`) and lifted operation $F[\Box -]$ (`liftBoxMap`) satisfy the size-indexed functor laws.
--   2. **Lemma 19**: The size-indexed $F[\Box -]$-coalgebra $(\nu^\Box F, \mathsf{out}^\Box)$ (`nuBoxCoalg`) is a terminal $F[\Box -]$-coalgebra.
--   3. **Lemma 20 & Proposition 22**: Constant size-indexing $T$ and universal quantification $\forall$ lift coalgebra morphisms between $F\text{-}\mathsf{Coalg}$ and $F[\Box -]\text{-}\mathsf{CoAlg}$ and form an adjunction $T \dashv \forall$ ($\mathrm{FCoalgHom}(X, \forall Y) \simeq \mathrm{SizedFCoalgHom}(T X, Y)$).
--   4. **Theorem 23 & Polynomial $M$-Type Corollary**: For any $F$ weakly commuting with $\forall$, `nuCoalg` with carrier $\nu F := \forall i.\,(\nu^\Box F)\,i$ is a terminal $F$-coalgebra with tracked half-adjoint equivalence structure map $\mathsf{out}$, and every polynomial endofunctor $P_{A, B}$ weakly commutes with $\forall$ and thus admits a terminal coalgebra ($M$-type).
-- source:
--   Bastiaan Laarakker, Daniël Otten, and Benno van den Berg, 'Constructing (Co)inductive Types via Large Sizes', FSCD 2026 (arXiv:2602.18921), Section 3.2, 3.4 & Appendix B, Proposition 5, Lemmas 19–20, Proposition 22, Theorem 23 (pp. 9, 24–27)

import Definitions.Def_LaarakkerOttenVanDenBerg2026_Encoding

namespace LaarakkerOttenVanDenBerg2026

universe u v

theorem theorem_23_coinductive_types
    (P : ParametricSizeTheory.{u, v}) :
    (∀ (F : WildEndofunctor P.toSizeCoreTheory),
      (∀ (A : SizeTy P.toSizeCoreTheory) (i : P.Size) (x : P.El (P.boxU A i)),
        boxMap P.toSizeCoreTheory (sizeHomId P.toSizeCoreTheory A) i x = x) ∧
      (∀ {A B C : SizeTy P.toSizeCoreTheory}
        (g : SizeHom P.toSizeCoreTheory B C) (f : SizeHom P.toSizeCoreTheory A B)
        (i : P.Size) (x : P.El (P.boxU A i)),
        boxMap P.toSizeCoreTheory (sizeHomComp P.toSizeCoreTheory g f) i x =
          boxMap P.toSizeCoreTheory g i (boxMap P.toSizeCoreTheory f i x)) ∧
      (∀ (A : SizeTy P.toSizeCoreTheory) (i : P.Size)
        (x : P.El (liftBoxObj P.toSizeCoreTheory F A i)),
        liftBoxMap P.toSizeCoreTheory F (sizeHomId P.toSizeCoreTheory A) i x = x) ∧
      (∀ {A B C : SizeTy P.toSizeCoreTheory}
        (g : SizeHom P.toSizeCoreTheory B C) (f : SizeHom P.toSizeCoreTheory A B)
        (i : P.Size) (x : P.El (liftBoxObj P.toSizeCoreTheory F A i)),
        liftBoxMap P.toSizeCoreTheory F (sizeHomComp P.toSizeCoreTheory g f) i x =
          liftBoxMap P.toSizeCoreTheory F g i (liftBoxMap P.toSizeCoreTheory F f i x)) ∧
      Nonempty (IsTerminalSizedFCoalg P.toSizeCoreTheory (nuBoxCoalg P.toSizeCoreTheory F)) ∧
      (∀ {X Y : FCoalg F} (f : FCoalgHom X Y) (i : P.Size)
        (c : P.El ((constSizedFCoalg P.toSizeCoreTheory X).carrier i)),
        (constSizedFCoalg P.toSizeCoreTheory Y).str i
            (constSizeHom P.toSizeCoreTheory f.hom i c) =
          liftBoxMap P.toSizeCoreTheory F (constSizeHom P.toSizeCoreTheory f.hom) i
            ((constSizedFCoalg P.toSizeCoreTheory X).str i c)) ∧
      (∀ (hF : WeaklyCommutesAll P.toSizeCoreTheory F)
        {C D : SizedFCoalg P.toSizeCoreTheory F}
        (g : SizedFCoalgHom P.toSizeCoreTheory C D)
        (x : P.El (allFCoalg P.toSizeCoreTheory hF C).carrier),
        (allFCoalg P.toSizeCoreTheory hF D).str (allMap P.toSizeCoreTheory g.hom x) =
          F.map (allMap P.toSizeCoreTheory g.hom)
            ((allFCoalg P.toSizeCoreTheory hF C).str x)) ∧
      (∀ (hF : WeaklyCommutesAll P.toSizeCoreTheory F)
        (X : FCoalg F) (Y : SizedFCoalg P.toSizeCoreTheory F),
        Nonempty (FCoalgHom X (allFCoalg P.toSizeCoreTheory hF Y) ≃
          SizedFCoalgHom P.toSizeCoreTheory (constSizedFCoalg P.toSizeCoreTheory X) Y)) ∧
      (∀ (hF : WeaklyCommutesAll P.toSizeCoreTheory F),
        Nonempty (IsTerminalFCoalg (nuCoalg P.toSizeCoreTheory hF)) ∧
        Nonempty (IsTrackedHAEquiv P.toSizeCoreTheory (nuCoalg P.toSizeCoreTheory hF).str))) ∧
    (∀ (A : P.U) (B : P.El A → P.U),
      ∃ (hPoly : WeaklyCommutesAll P.toSizeCoreTheory
          (polyEndofunctor P.toSizeCoreTheory A B)),
        Nonempty (IsTerminalFCoalg (nuCoalg P.toSizeCoreTheory hPoly)) ∧
        Nonempty (IsTrackedHAEquiv P.toSizeCoreTheory (nuCoalg P.toSizeCoreTheory hPoly).str)) := by
  sorry

end LaarakkerOttenVanDenBerg2026
