-- Prove2me | Theorems.Thm_NondualOpt_lemma_27
-- name    : NondualOpt.lemma_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:59:22.028754+00:00
-- url     : https://prove2.me/theorems/5b636c06-db8e-464d-8ae8-28198e87b087
-- title:
--   Lemma 27 — sequential union bound
-- statement:
--   Let $G_1,\dots,G_N$ ($N\ge1$) be real-valued function classes on the same domain and $G=\bigcup_{i=1}^NG_i$. If $\mathrm{sfat}_\alpha(G_i)\le m$ for every $i\in[N]$, then
--   $$
--   \mathrm{sfat}_\alpha(G)\le C\,(m+\log N)
--   $$
--   for a universal constant $C$. Covering a ball by $N$ local balls therefore costs only $\log N$ in sequential fat-shattering, which is the combination step of Proposition 28.
--
--   Differences from the source:
--   - encoding: m → a natural number m; reason: sfat is integer-valued, so sfat ≤ m for real m ≥ 0 is sfat ≤ ⌊m⌋
--   - encoding: G_1, …, G_N, α → N ≥ 1, indices Fin N, α > 0 (Definition 1), C chosen before the domain and the classes; reason: the paper's setting and quantifier order
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Lemma 27, p.38

import Mathlib
import Definitions.Def_NondualOpt_sfat

open scoped ENNReal

universe u

namespace NondualOpt

/-- **Lemma 27 (Sequential union bound).** Let `G_1, …, G_N` be real-valued function classes on the
same domain and `G = ⋃_i G_i`. If `sfat_α(G_i) ≤ m` for every `i ∈ [N]`, then
`sfat_α(G) ≤ C(m + log N)` for a universal constant `C`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Lemma 27, p.38.

**Formalization Note.** `C` is chosen before the domain, the classes, `N`, `α` and `m`. `N ≥ 1`
(the classes `G_1, …, G_N`), `α > 0` (Definition 1), and `m` is a natural number (`sfat` is
integer-valued, so `sfat ≤ m` for a real `m ≥ 0` is `sfat ≤ ⌊m⌋`). Indices are `Fin N`. -/
theorem lemma_27 :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : Type u) (N : ℕ), 1 ≤ N → ∀ (G : Fin N → Set (Z → ℝ)) (α : ℝ),
      0 < α → ∀ m : ℕ, (∀ i, sfat (G i) α ≤ m) →
        (sfat (⋃ i, G i) α : ℝ≥0∞) ≤ ENNReal.ofReal (C * (m + Real.log N)) := by sorry

end NondualOpt
