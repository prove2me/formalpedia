-- Prove2me | Theorems.Thm_MultiphaseDisj_claim_4_4
-- name    : MultiphaseDisj.claim_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:11.070872+00:00
-- url     : https://prove2.me/theorems/fb36a5a4-31db-4857-9858-14ff66e0eb0f
-- title:
--   Claim 4.4 — a chain of rows with new elements
-- statement:
--   Let $\varepsilon=1/40$, let $s\ge200$, let $N$ be a multiple of $s^2$ and $\mathcal S=\binom{[N]}{s}$, and put
--   $$
--   r=N/s^2,\qquad k=\lceil s/2\rceil,\qquad g=\lfloor s/6\rfloor,\qquad t=rg .
--   $$
--   If $A'\subseteq\mathcal S$ satisfies $|A'|\ge2^{-\varepsilon s-1}|\mathcal S|$, then there are $a_1,\dots,a_t\in A'$ and sets $D_1,\dots,D_t$ such that, for every $j\in[t]$,
--   $$
--   D_j\subseteq a_j\setminus(a_1\cup\dots\cup a_{j-1})\qquad\text{and}\qquad |D_j|=k .
--   $$
--   In particular, $D_1,\dots,D_t$ are pairwise disjoint.
--
--   This is the chain step of the corruption bound: a large family of sparse sets contains $\Theta(N/s)$ rows each bringing $\lceil s/2\rceil$ new elements.
--
--   Differences from the source:
--   - generalization: A′ the good rows {a ∈ A : Pr_{b∼U_B}[a ∩ b ≠ ∅] ≤ 2δ} of the proof of Lemma 4.1 → any A′ ⊆ ([N] choose s) with |A′| ≥ 2^{−εs−1}|S|; reason: the proof (p.27) uses only these two properties, which the good rows have (p.26)
--   - encoding: indices j ∈ [t], ⌈s/2⌉, ⌊s/6⌋, N/s² → Fin t (0-based), (s + 1)/2, s/6 and N/s² in ℕ; reason: same values; N/s² is exact since s² ∣ N
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Claim 4.4, p.26 (proof p.27)

import Mathlib
import Definitions.Def_MultiphaseDisj_Rectangle

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Claim 4.4 (A chain of rows with new elements)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Claim 4.4, p.26; proof p.27). Let
`ε := 1/40`, `s ≥ 200`, `N` a multiple of `s²`, `S := ([N] choose s)`, and put `r := N/s²`,
`k := ⌈s/2⌉`, `g := ⌊s/6⌋`, `t := rg`. If `A′ ⊆ S` has `|A′| ≥ 2^{−εs−1} |S|`, there are
`a_1, …, a_t ∈ A′` and sets `D_1, …, D_t` such that, for every `j ∈ [t]`,
`D_j ⊆ a_j \ (a_1 ∪ ⋯ ∪ a_{j−1})` and `|D_j| = k`. In particular, `D_1, …, D_t` are pairwise
disjoint.

**Formalization Note** In the paper `A′` is the set of good rows of the proof of Lemma 4.1 (p.26);
its proof (p.27) uses only `A′ ⊆ S` and `|A′| ≥ 2^{−εs−1} |S|`, which are the hypotheses here.
Indices `j ∈ [t]` are `Fin t` (`0`-based); `⌈s/2⌉ = (s + 1)/2` and `⌊s/6⌋ = s/6` in `ℕ`. -/
theorem claim_4_4 (N s : ℕ) (hs : 200 ≤ s) (hN : s ^ 2 ∣ N) (A' : Finset (Finset (Fin N)))
    (hA'S : A' ⊆ Finset.powersetCard s (Finset.univ : Finset (Fin N)))
    (hA' : (2 : ℝ) ^ (-(1 / 40 : ℝ) * s - 1) *
        ((Finset.powersetCard s (Finset.univ : Finset (Fin N))).card : ℝ) ≤ (A'.card : ℝ)) :
    ∃ a D : Fin (N / s ^ 2 * (s / 6)) → Finset (Fin N),
      (∀ j, a j ∈ A') ∧
      (∀ j, D j ⊆ a j \ (Finset.univ.filter (fun j' => j' < j)).biUnion a ∧
        (D j).card = (s + 1) / 2) ∧
      (∀ j j', j ≠ j' → Disjoint (D j) (D j')) := by sorry

end MultiphaseDisj
