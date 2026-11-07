-- Prove2me | Theorems.Thm_MultiphaseDisj_corollary_3_12
-- name    : MultiphaseDisj.corollary_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:29.495633+00:00
-- url     : https://prove2.me/theorems/6389154e-a450-47b0-8794-1d53239da17c
-- title:
--   Corollary 3.12 — high min-entropy rectangles are not monochromatic
-- statement:
--   Let $\varepsilon=1/40$ and $c=1/100$. Let $s\ge200$, let $N$ be a multiple of $s^2$, let $\mathcal S=\binom{[N]}{s}$, and let $\nu_A,\nu_B$ be distributions on $\mathcal S$ with
--   $$
--   H_\infty(\nu_A),\ H_\infty(\nu_B)\ \ge\ \log|\mathcal S|-(\varepsilon s-1).
--   $$
--   Then
--   $$
--   \Pr_{a\sim\nu_A,\ b\sim\nu_B}\big[a\cap b\neq\emptyset\big]\ge\frac{cs^2}N ,
--   $$
--   with $a$ and $b$ independent.
--
--   This is Step 4 of the proof: the rectangle of Corollary 3.11 would put mass at most $n^{-1/10}$ on intersecting pairs, while this bound gives mass at least $c/\ell$.
--
--   Differences from the source:
--   - encoding: [N]; min-entropy and log base 2; a ∼ ν_A, b ∼ ν_B → Fin N; logb 2; the product ν_A ⊗ ν_B; reason: same instances
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Corollary 3.12, p.24 (restated and proved p.25)

import Mathlib
import Definitions.Def_MultiphaseDisj_Rectangle

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Corollary 3.12 (High min-entropy rectangles are not monochromatic)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Corollary 3.12,
p.24; restated and proved p.25). Let `ε := 1/40` and `c := 1/100`. Let `s ≥ 200`, let `N` be a
multiple of `s²`, let `S := ([N] choose s)`, and let `ν_A, ν_B` be distributions on `S` with
`H∞(ν_A), H∞(ν_B) ≥ log |S| − (εs − 1)`. Then `Pr_{a∼ν_A, b∼ν_B}[a ∩ b ≠ ∅] ≥ c s²/N`.

**Formalization Note** `[N]` is `Fin N`; min-entropy and `log` are base 2; `a ∼ ν_A` and `b ∼ ν_B`
are independent (the product `ν_A ⊗ ν_B`). -/
theorem corollary_3_12 (N s : ℕ) (hs : 200 ≤ s) (hN : s ^ 2 ∣ N)
    (νA νB : Finset (Fin N) → ℝ)
    (hνA : IsDistOn (Finset.powersetCard s (Finset.univ : Finset (Fin N))) νA)
    (hνB : IsDistOn (Finset.powersetCard s (Finset.univ : Finset (Fin N))) νB)
    (hA : Real.logb 2 ((Finset.powersetCard s (Finset.univ : Finset (Fin N))).card : ℝ) -
        ((1 / 40 : ℝ) * s - 1) ≤ minEntropy νA)
    (hB : Real.logb 2 ((Finset.powersetCard s (Finset.univ : Finset (Fin N))).card : ℝ) -
        ((1 / 40 : ℝ) * s - 1) ≤ minEntropy νB) :
    (1 / 100 : ℝ) * (s : ℝ) ^ 2 / N ≤ pr (prodDist νA νB) (fun p => ¬ Disjoint p.1 p.2) := by sorry

end MultiphaseDisj
