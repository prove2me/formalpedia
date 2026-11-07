-- Prove2me | Theorems.Thm_MultiphaseDisj_lemma_4_1
-- name    : MultiphaseDisj.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:17.553238+00:00
-- url     : https://prove2.me/theorems/03ae2f91-66bd-4474-afec-9bc084c3ec3a
-- title:
--   Lemma 4.1 — corruption for sparse sets
-- statement:
--   Let $\varepsilon=1/40$ and $c=1/100$. Let $s\ge200$, let $N$ be a multiple of $s^2$, and let $\mathcal S=\binom{[N]}{s}$. If $A,B\subseteq\mathcal S$ satisfy $|A|,|B|\ge2^{-\varepsilon s}|\mathcal S|$, then
--   $$
--   \Pr_{a\sim U_A,\ b\sim U_B}\big[a\cap b\neq\emptyset\big]\ge c\cdot\frac{s^2}N ,
--   $$
--   where $U_A,U_B$ are the uniform distributions on $A$ and $B$, drawn independently.
--
--   For $N=s^2$ this is the rectangle bound of Babai, Frankl and Simon behind the $\Omega(\sqrt N)$ lower bound for Disjointness; the lemma extends it to sparser sets. The bound is one-sided: the analogous lower bound on the probability of disjointness is false.
--
--   **Formalization Note** $N=0$ is a multiple of $s^2$ that the paper does not intend; there both sides are $0$ in Lean, so no hypothesis $N>0$ is needed.
--
--   Differences from the source:
--   - encoding: [N], U_A ⊗ U_B → Fin N and the product of the uniform laws on A and B; reason: same instances
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Lemma 4.1, p.24 (proof pp.26–27)

import Mathlib
import Definitions.Def_MultiphaseDisj_Rectangle

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Lemma 4.1 (Corruption for sparse sets)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Lemma 4.1, p.24; proof pp.26–27). Let
`ε := 1/40` and `c := 1/100`. Let `s ≥ 200`, let `N` be a multiple of `s²`, and write
`S := ([N] choose s)`. If `A, B ⊆ S` satisfy `|A|, |B| ≥ 2^{−εs} |S|`, then
`Pr_{a∼U_A, b∼U_B}[a ∩ b ≠ ∅] ≥ c · s²/N`, where `U_A`, `U_B` are the uniform distributions on `A`
and `B`.

**Formalization Note** `[N]` is `Fin N`. The probability is under the product `U_A ⊗ U_B`. At
`N = 0` (a multiple of `s²` the paper does not intend) both sides are `0` in Lean. -/
theorem lemma_4_1 (N s : ℕ) (hs : 200 ≤ s) (hN : s ^ 2 ∣ N) (A B : Finset (Finset (Fin N)))
    (hAS : A ⊆ Finset.powersetCard s (Finset.univ : Finset (Fin N)))
    (hBS : B ⊆ Finset.powersetCard s (Finset.univ : Finset (Fin N)))
    (hA : (2 : ℝ) ^ (-(1 / 40 : ℝ) * s) *
        ((Finset.powersetCard s (Finset.univ : Finset (Fin N))).card : ℝ) ≤ (A.card : ℝ))
    (hB : (2 : ℝ) ^ (-(1 / 40 : ℝ) * s) *
        ((Finset.powersetCard s (Finset.univ : Finset (Fin N))).card : ℝ) ≤ (B.card : ℝ)) :
    (1 / 100 : ℝ) * ((s : ℝ) ^ 2 / N) ≤
      pr (prodDist (unif A) (unif B)) (fun p => ¬ Disjoint p.1 p.2) := by sorry

end MultiphaseDisj
