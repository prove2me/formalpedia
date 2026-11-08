-- Prove2me | Theorems.Thm_LaarakkerOttenVanDenBerg2026_lemmas_7_8_and_prop_10
-- name    : LaarakkerOttenVanDenBerg2026.lemmas_7_8_and_prop_10
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-07T15:42:32.822752+00:00
-- url     : https://prove2.me/theorems/8c48495e-4674-4795-ad9d-533e17e15221
-- title:
--   Proposition 4, Lemmas 7–8, and Proposition 10: Size-Indexed Initial Algebras and Adjoint Lifting Functors
-- statement:
--   **Proposition 4 (p. 9), Lemma 7 (p. 10 & p. 24), Lemma 8 (p. 11), and Proposition 10 (p. 11)**:
--   For any core size theory $T$ and wild endofunctor $F : U \to U$:
--   1. **Proposition 4**: The bounded existential modality $\Diamond$ (`diamondMap`) and lifted operation $F[\Diamond -]$ (`liftDiamondMap`) satisfy the size-indexed functor laws.
--   2. **Lemma 7**: The size-indexed $F[\Diamond -]$-algebra $(\mu^\Diamond F, \mathsf{in}^\Diamond)$ (`muDiamondAlg T F`) is an initial $F[\Diamond -]$-algebra.
--   3. **Lemma 8**: Constant size-indexing $T A := \lambda i.\,A$ lifts every $F$-algebra morphism to a size-indexed $F[\Diamond -]$-algebra morphism (`constSizedFAlg`).
--   4. **Proposition 10**: If $F$ weakly commutes with $\exists$, existential quantification lifts every size-indexed $F[\Diamond -]$-algebra morphism to an $F$-algebra morphism (`exFAlg`) and is left adjoint to $T$ ($\mathrm{FAlgHom}(\exists X, Y) \simeq \mathrm{SizedFAlgHom}(X, T Y)$).
-- source:
--   Bastiaan Laarakker, Daniël Otten, and Benno van den Berg, 'Constructing (Co)inductive Types via Large Sizes', FSCD 2026 (arXiv:2602.18921), Section 3.2–3.3, Proposition 4, Lemmas 7–8, Proposition 10 (pp. 9–11) & Appendix B (p. 24)

import Definitions.Def_LaarakkerOttenVanDenBerg2026_Encoding

namespace LaarakkerOttenVanDenBerg2026

universe u v

theorem lemmas_7_8_and_prop_10
    (T : SizeCoreTheory.{u, v})
    (F : WildEndofunctor T) :
    (∀ (A : SizeTy T) (i : T.Size) (x : T.El (T.diamondU A i)),
      diamondMap T (sizeHomId T A) i x = x) ∧
    (∀ {A B C : SizeTy T} (g : SizeHom T B C) (f : SizeHom T A B)
      (i : T.Size) (x : T.El (T.diamondU A i)),
      diamondMap T (sizeHomComp T g f) i x = diamondMap T g i (diamondMap T f i x)) ∧
    (∀ (A : SizeTy T) (i : T.Size) (x : T.El (liftDiamondObj T F A i)),
      liftDiamondMap T F (sizeHomId T A) i x = x) ∧
    (∀ {A B C : SizeTy T} (g : SizeHom T B C) (f : SizeHom T A B)
      (i : T.Size) (x : T.El (liftDiamondObj T F A i)),
      liftDiamondMap T F (sizeHomComp T g f) i x =
        liftDiamondMap T F g i (liftDiamondMap T F f i x)) ∧
    Nonempty (IsInitialSizedFAlg T (muDiamondAlg T F)) ∧
    (∀ {X Y : FAlg F} (f : FAlgHom X Y) (i : T.Size)
      (z : T.El (liftDiamondObj T F (constSizedFAlg T X).carrier i)),
      constSizeHom T f.hom i ((constSizedFAlg T X).str i z) =
        (constSizedFAlg T Y).str i (liftDiamondMap T F (constSizeHom T f.hom) i z)) ∧
    (∀ (hF : WeaklyCommutesEx T F) {X Y : SizedFAlg T F} (f : SizedFAlgHom T X Y)
      (z : T.El (F.obj (exFAlg T hF X).carrier)),
      exMap T f.hom ((exFAlg T hF X).str z) =
        (exFAlg T hF Y).str (F.map (exMap T f.hom) z)) ∧
    (∀ (hF : WeaklyCommutesEx T F) (X : SizedFAlg T F) (Y : FAlg F),
      Nonempty (FAlgHom (exFAlg T hF X) Y ≃ SizedFAlgHom T X (constSizedFAlg T Y))) := by
  sorry

end LaarakkerOttenVanDenBerg2026
