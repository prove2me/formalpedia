-- Prove2me | Theorems.Thm_JardenShami_arrow_la_of_arrow_add_of_card
-- name    : JardenShami.arrow_la_of_arrow_add_of_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:13.03057+00:00
-- url     : https://prove2.me/theorems/76e37265-e976-4477-a5c5-f5dc0c4dc9b2
-- title:
--   Jarden Shami: arrow la of arrow add of card
-- statement:
--   AUX: not in paper. The argument of the paper's proof of Theorem 3.1, for a general bound on
--   the number of colors. `Q` bounds the colors allowed in the hypothesis (additive colorings) and
--   `P` those in the conclusion (locally additive colorings). If every `D` allowed by `P` and the set
--   of colors `D* = D → Option D` (the partial functions `u_{a,b} : D_b → D`) are allowed by `Q`,
--   then `F → (F)_{add, Q}` implies `F → (F)_{la, P}`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section3.lean#L84-L165
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section3.lean#L84-L165

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
variable {X : Type w} [LinearOrder X]

theorem JardenShami.arrow_la_of_arrow_add_of_card (P Q : Cardinal.{v} → Prop)
    (hPQ : ∀ D : Type v, P #D → Q #D ∧ Q #(D → Option D)) (F : Set (Set X))
    (h : Arrow F F (fun _ D C => IsAdditive C ∧ Q #D)) :
    Arrow F F (fun _ D C => IsLocallyAdditive C ∧ P #D) := by sorry
