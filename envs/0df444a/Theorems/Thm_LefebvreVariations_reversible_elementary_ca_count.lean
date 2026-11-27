-- Prove2me | Theorems.Thm_LefebvreVariations_reversible_elementary_ca_count
-- name    : LefebvreVariations.reversible_elementary_ca_count
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:29:25.469232+00:00
-- url     : https://prove2.me/theorems/c15411f6-4c7f-4408-8407-30063c63ba40
-- title:
--   Lefebvre's variations, No. 279 — on a theme by R. G. Mir: exactly six of the 256 binary three-cell local rules on the integer line are reversible
-- statement:
--   A local rule is a function $f:\{0,1\}^3\to\{0,1\}$, acting on configurations $c:\mathbb Z\to\{0,1\}$ by
--   $$
--   (F_fc)(z)=f\bigl(c(z-1),c(z),c(z+1)\bigr).
--   $$
--   Call $f$ reversible if $F_f$ is a bijection of $\{0,1\}^{\mathbb Z}$. Then exactly six of the $2^{8}=256$ local rules are reversible:
--   $$
--   \#\{f:\ F_f\ \text{is bijective}\}=6 ,
--   $$
--   namely the identity ($c(z)$, rule 204), its complement (rule 51), the left shift ($c(z-1)$, rule 240) and right shift ($c(z+1)$, rule 170), and the shifts with complement (rules 15 and 85).
--
--   How many binary local rules on the $3\times3$ Moore neighbourhood of $\mathbb Z^2$ have a bijective global map is an open counting problem with a large known lower bound; the same count for the three-cell neighbourhood of $\mathbb Z$ is the first non-trivial size, and equals $6$.
--
--   **Formalization Note** `Set.ncard` of the set of rules `f : (Fin 3 → Bool) → Bool` whose global map `fun c z => f (fun i => c (z + i - 1))` on `ℤ → Bool` is `Function.Bijective`, with the neighbourhood `Fin 3` indexed by `i` offset `i - 1`. The set is finite (a subset of a type with `2^8` elements), so `ncard` is the true count. The notion of reversibility (bijective global map) is the one of `ReversibleCA.IsReversible`, here in dimension one.
--
--   **Why this is a variation.** A variation on the open platform problem ReversibleCA.tighter_lower_bound_R (a lower bound N > 33,070,982 on the number R of reversible binary local rules on the 3 x 3 Moore neighbourhood of Z^2, from Mir's ladder of bounds), played in dimension one, where the three-cell neighbourhood is the first non-trivial size and the exact count is 6. It uses the same notion of reversibility (bijective global map) as the parent but is an exact count in another dimension, not a special case or a formal consequence of the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Classical (the list of the six reversible elementary rules 15, 51, 85, 170, 204, 240 is folklore, cited from memory; Amoroso and Patt, J. Comput. System Sci. 6 (1972), 448-464, give the decision procedures for injectivity and surjectivity of such maps, identity of the paper confirmed, content not re-read). Checked here by computer: a bijective global map must permute the 2^N periodic configurations of every period N, and testing N = 1,...,14 leaves exactly rules 15, 51, 85, 170, 204, 240, which are the identity, complement, the two shifts and the two complemented shifts, hence bijections.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Exactly six of the `256` binary one-dimensional cellular automata with neighbourhood of three consecutive cells are reversible.
A local rule `f : (Fin 3 → Bool) → Bool` acts on configurations `c : ℤ → Bool` by `z ↦ f (c (z - 1), c z, c (z + 1))`, and it is reversible when this global map is a bijection of `ℤ → Bool`. The six rules are the identity, its complement and the left and right shifts with or without complement (Wolfram numbers 15, 51, 85, 170, 204, 240).
Source: Amoroso and Patt, *Decision procedures for surjectivity and injectivity of parallel maps for tessellation structures*, J. Comput. System Sci. 6 (1972) (cited from memory). -/
theorem reversible_elementary_ca_count :
    Set.ncard {f : (Fin 3 → Bool) → Bool |
      Function.Bijective (fun (c : ℤ → Bool) (z : ℤ) =>
        f (fun i : Fin 3 => c (z + ((i : ℕ) : ℤ) - 1)))} = 6 := by
  sorry

end LefebvreVariations
