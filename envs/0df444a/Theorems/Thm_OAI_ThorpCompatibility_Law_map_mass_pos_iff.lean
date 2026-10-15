-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_Law_map_mass_pos_iff
-- name    : OAI.ThorpCompatibility.Law.map_mass_pos_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:43:22.094597+00:00
-- url     : https://prove2.me/theorems/27139122-2eb1-456b-8ce0-739a2ec66e38
-- title:
--   Support of the pushforward of a finite probability law
-- statement:
--   Let $\Omega$ and $\mathcal B$ be finite sets, let $P$ be a probability distribution on $\Omega$ and let $f:\Omega\to\mathcal B$. The pushforward law $P_f$ on $\mathcal B$ has masses $P_f(b)=\sum_{\omega\in\Omega:\,f(\omega)=b}P(\omega)$. For every $b\in\mathcal B$,
--
--   $$
--   P_f(b)>0\quad\Longleftrightarrow\quad\text{there is }\omega\in\Omega\text{ with }f(\omega)=b\text{ and }P(\omega)>0 .
--   $$
--
--   In words, the support of the image law is the image of the support. This is used throughout the finite entropy calculus to verify absolute-continuity hypotheses (that a reference law vanishes only where the law of interest vanishes) for laws of random variables.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/ConditionalEntropy.lean#L12-L24

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy

open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem OAI.ThorpCompatibility.Law.map_mass_pos_iff (P : Law α) (f : α → β) (b : β) :
    0 < (P.map f).mass b ↔ ∃ a, f a = b ∧ 0 < P.mass a := by sorry
