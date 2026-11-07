-- Prove2me | Theorems.Thm_HypercliqueFalse_counting_identity
-- name    : HypercliqueFalse.counting_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:32:15.410284+00:00
-- url     : https://prove2.me/theorems/f7adfa60-b676-48b4-aec9-6a4494363ff3
-- title:
--   Section 2 — $H_{k,h}$ is $k!$ times the number of $k$-hypercliques
-- statement:
--   Let $2 \le h \le k$ and let $G = ([n], E)$ be an $h$-uniform hypergraph. If all arrays $A_S$ are equal to the $0$-$1$ array $\mathbf 1_E$ indicating the hyperedges, then
--   $$
--   H_{k,h} = \sum_{x\in[n]^k}\ \prod_{S\in\binom{[k]}{h}} \mathbf 1_E(x_S) = k!\cdot\#\{k\text{-hypercliques of } G\},
--   $$
--   and in particular $G$ contains a $k$-hyperclique if and only if $H_{k,h} > 0$.
--
--   This reduces hyperclique detection (Theorem 1.1) to evaluating $H_{k,h}$ (Theorem 2.1).
--
--   Differences from the source:
--   - reading: the sentence carries no range (it is used for k > h ≥ 2, Theorem 2.1) → 2 ≤ h ≤ k; reason: the sentence is false for h = 1 (h = 1, k = 2, n = 1, E = {{1}}: H = 1 but there is no 2-hyperclique) and for 2 ≤ k < h (empty product); k = h is included since it holds there
--   - encoding: the number of k-hypercliques → Set.ncard of the set of k-hypercliques; reason: the set is finite; same number
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, Hyperclique Polynomials, p.4

import Mathlib
import Definitions.Def_HypercliqueFalse_IsHyperclique
import Definitions.Def_HypercliqueFalse_edgeIndicator
import Definitions.Def_HypercliqueFalse_hyperPoly

set_option autoImplicit false

namespace HypercliqueFalse

/-- **`H_{k,h}` counts hypercliques.** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Section 2, p.4: "If all arrays A_S are
equal to the 0-1-array indicating the hyperedges in E, then H_{k,h} is exactly k! times the number
of k-hypercliques in G. In particular, G contains a k-hyperclique if and only if H_{k,h} > 0."

For `2 ≤ h ≤ k` and every `h`-uniform hypergraph `G` on `[n]`.

**Formalization Note.** The sentence carries no range; it is used for `k > h ≥ 2` (Theorem 2.1). It
fails for `h = 1` (tuples with repeated vertices are counted) and for `2 ≤ k < h` (the product is
empty); `k = h` is included since it holds there. The number of hypercliques is `Set.ncard`. -/
theorem counting_identity (n h k : ℕ) (hh : 2 ≤ h) (hk : h ≤ k) (G : Hypergraph n h) :
    hyperPoly (k := k) (m := n) (fun _ y => edgeIndicator G y) =
        (k.factorial : ℤ) * ({s : Finset (Fin n) | IsHyperclique G k s}.ncard : ℤ) ∧
      ((∃ s, IsHyperclique G k s) ↔
        0 < hyperPoly (k := k) (m := n) (fun _ y => edgeIndicator G y)) := by sorry

end HypercliqueFalse
