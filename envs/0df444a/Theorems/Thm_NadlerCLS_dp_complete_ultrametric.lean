-- Prove2me | Theorems.Thm_NadlerCLS_dp_complete_ultrametric
-- name    : NadlerCLS.dp_complete_ultrametric
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:55:51.376334+00:00
-- url     : https://prove2.me/theorems/ddecf9d8-b964-434c-a832-b3e878c04f5f
-- title:
--   $d_p$ is a complete ultrametric (proof of Lemma C.8)
-- statement:
--   Let $X$ be a set and $p:X\to[0,1]$. The function $d_p$ of (C.8) satisfies
--
--   1. $d_p(x,y)=0\iff x=y$;
--   2. $d_p(x,y)=d_p(y,x)$;
--   3. $d_p(x,z)\le\max\{d_p(x,y),d_p(y,z)\}$ (ultrametric inequality);
--   4. $1\le d_p(x,y)\le2$ whenever $x\ne y$;
--   5. every $d_p$-Cauchy sequence is eventually constant, and hence converges in $d_p$.
--
--   So $(X,d_p)$ is a complete ultrametric space; this is why the instances of the hardness reduction satisfy the metric and completeness promise.
--
--   Differences from the source:
--   - generalization: $X=[0,1]^n$ → an arbitrary type; reason: the argument uses no structure of the cube
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), proof of Lemma C.8, p.39

import Mathlib
import Definitions.Def_NadlerCLS_dp

set_option autoImplicit false

namespace NadlerCLS

open Filter Topology

/-- **`d_p` is a complete ultrametric with values in `{0} ∪ [1, 2]`** (Xiong–Vlatakis-Gkaragkounis,
*On the Complexity of Finding Fixed Points for Set-Valued Contractions*, arXiv:2609.14101, held
version of 2026-11-03, sha256 1fcc5a02…6dc485, proof of Lemma C.8, p.39: "For completeness, dp is a
genuine complete ultrametric … Every nonzero distance is within [1, 2], so every dp-Cauchy sequence
is eventually constant"). For any set `α` and `p : α → [0, 1]`, the function `d_p` of (C.8)
satisfies: `d_p(x, y) = 0 ↔ x = y`; symmetry; the ultrametric inequality
`d_p(x, z) ≤ max{d_p(x, y), d_p(y, z)}`; `1 ≤ d_p(x, y) ≤ 2` for `x ≠ y`; every `d_p`-Cauchy sequence
is eventually constant and converges in `d_p`.

**Formalization Note** `α` is an arbitrary type (the paper's `X = [0, 1]ⁿ`). -/
theorem dp_complete_ultrametric {α : Type*} (p : α → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    (∀ x y, dp p x y = 0 ↔ x = y) ∧
    (∀ x y, dp p x y = dp p y x) ∧
    (∀ x y z, dp p x z ≤ max (dp p x y) (dp p y z)) ∧
    (∀ x y, x ≠ y → 1 ≤ dp p x y ∧ dp p x y ≤ 2) ∧
    (∀ u : ℕ → α, (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ a ≥ N, ∀ b ≥ N, dp p (u a) (u b) < ε) →
      (∃ N : ℕ, ∀ a ≥ N, u a = u N) ∧
      ∃ x, Tendsto (fun a => dp p (u a) x) atTop (𝓝 0)) := by sorry

end NadlerCLS
