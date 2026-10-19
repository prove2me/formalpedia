-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_Pairing_exists_perm_fixing_pair
-- name    : OAI.MatchingSmoothing.Pairing.exists_perm_fixing_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:30:23.017768+00:00
-- url     : https://prove2.me/theorems/ea88cd85-fd96-4382-b0e0-42995ea0f528
-- title:
--   The pointwise stabiliser of a set acts 2-transitively on its complement
-- statement:
--   Let $\alpha$ be a finite set and $U\subseteq\alpha$. Let $a,b,c,d\in\alpha\setminus U$ with $a\ne b$ and $c\ne d$. Then some permutation of $\alpha$ fixes every point of $U$ and maps $a$ to $c$ and $b$ to $d$:
--
--   $$
--   \exists\,p\in\mathrm{Sym}(\alpha):\qquad p(u)=u\ \ (u\in U),\qquad p(a)=c,\qquad p(b)=d .
--   $$
--
--   The pairs $\{a,b\}$ and $\{c,d\}$ may overlap. In other words, the pointwise stabiliser of $U$ in $\mathrm{Sym}(\alpha)$ acts 2-transitively on $\alpha\setminus U$. In the analysis of functions on perfect matchings, this moves an arbitrary pair of vertices lying outside the first $t$ standard pairs onto the next standard pair, without disturbing the first $t$ pairs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/Pairings.lean#L379-L396

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings

open OAI OAI.MatchingSmoothing OAI.MatchingSmoothing.Pairing
universe u_1 u_2
variable {α : Type u_2}

theorem OAI.MatchingSmoothing.Pairing.exists_perm_fixing_pair [Fintype α] [DecidableEq α]
    (U : Finset α) {a b c d : α} (ha : a ∉ U) (hb : b ∉ U)
    (hc : c ∉ U) (hd : d ∉ U) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ p : Equiv.Perm α, (∀ u ∈ U, p u = u) ∧ p a = c ∧ p b = d := by sorry
