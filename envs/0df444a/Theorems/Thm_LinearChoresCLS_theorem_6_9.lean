-- Prove2me | Theorems.Thm_LinearChoresCLS_theorem_6_9
-- name    : LinearChoresCLS.theorem_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:59:49.618686+00:00
-- url     : https://prove2.me/theorems/8742d9c9-5a48-41ee-b722-e85ba756aa1f
-- title:
--   Theorem 6.9 — target quadratic approximation by a gadget chain, remainder bound $12w_{jj'}t^3$
-- statement:
--   Let $I=(A,c,\varepsilon)$ with $n\ge1$ and $\varepsilon>0$, and consider the completed market $f(I)$ with the parameters (7.1) and (6.9). For every chain $0\le j<j'\le n$ and every $x\in[0,1]^n$,
--   $$
--   -\frac{w_{jj'}}2t^2(x_j-x_{j'})^2=P_{(j,j')}(x)+R_{(j,j')}(x).
--   $$
--   The remainder satisfies $|R_{(j,j')}(x+he_\ell)-R_{(j,j')}(x)|\le12w_{jj'}t^3|h|$ for every $\ell\in[n]$ and every coordinate segment from $x$ to $x+he_\ell$ in the box; moreover, for every feasible coordinate direction $\tilde v\in\{\pm e_\ell\}$ at $x$, the right directional derivative exists and $|R'_{(j,j')}(x;\tilde v)|\le12w_{jj'}t^3$.
--
--   The gadget chain realizes the negative squared difference $-\frac{w_{jj'}}2t^2(x_j-x_{j'})^2$ needed to turn the basic market's quadratic into $\frac\alpha2x^\top Ax$.
--
--   **Formalization Note** $P_{(j,j')}$ and $R_{(j,j')}=\tilde R+\hat R$ are the paper's explicit formulas, with gadget prices from the max–min rule; $x_0=0$. Ties of the max–min rule are not excluded.
--
--   Differences from the source:
--   - encoding: chains 0 ≤ j < j′ ≤ n, x₀ = 0 → π : Pair n (a subtype of Fin (n+1) × Fin (n+1)), x extended by Fin.cons 0; reason: index conventions; same instances
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Theorem 6.9, Eq. (6.11), p.24 (proof Appendix C.1, pp.46–47)

import Mathlib
import Definitions.Def_LinearChoresCLS_Remainders
import Definitions.Def_LinearChoresCLS_RightDeriv

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **Theorem 6.9 (Target quadratic approximation)** (arXiv:2611.06589, held version sha256
85d34a9e…, p.24). For the completed market `f(I)` of an instance `I = (A, c, ε)` (`n ≥ 1`,
`ε > 0`, parameters (7.1) and (6.9)) and every chain `0 ≤ j < j′ ≤ n`: for every `x ∈ [0,1]ⁿ`,
`−(w_{jj′}/2) t² (x_j − x_{j′})² = P_{(j,j′)}(x) + R_{(j,j′)}(x)` (6.11); the remainder satisfies
`|R_{(j,j′)}(x + he_ℓ) − R_{(j,j′)}(x)| ≤ 12 w_{jj′} t³ |h|` for every `ℓ ∈ [n]` and every coordinate
segment from `x` to `x + he_ℓ` in the box; and for every feasible coordinate direction
`ṽ ∈ {±e_ℓ}` at `x` the right directional derivative exists and `|R′_{(j,j′)}(x; ṽ)| ≤ 12 w_{jj′} t³`.

**Formalization Note.** `x₀ = 0`; `P_{(j,j′)}` is `chainAbs` and `R_{(j,j′)} = R̃ + R̂` is
`chainRem`, both from the paper's explicit formulas, with the gadget prices given by the max–min
rule. -/
theorem theorem_6_9 {n : ℕ} (hn : 0 < n) (P : Quadratic n) (ε : ℚ) (hε : 0 < ε) (π : Pair n) :
    (∀ x : Fin n → ℝ, InCube x →
      -(pairWeight P π / 2) * tParam P ε ^ 2 * (xExt x π.1.1 - xExt x π.1.2) ^ 2 =
        chainAbs P (tParam P ε) (chainLength P ε) π x +
          chainRem P (tParam P ε) (chainLength P ε) π x) ∧
    (∀ (x : Fin n → ℝ) (ℓ : Fin n) (h : ℝ), InCube x → InCube (x + h • Pi.single ℓ (1 : ℝ)) →
      |chainRem P (tParam P ε) (chainLength P ε) π (x + h • Pi.single ℓ (1 : ℝ)) -
          chainRem P (tParam P ε) (chainLength P ε) π x| ≤
        12 * pairWeight P π * tParam P ε ^ 3 * |h|) ∧
    (∀ (x : Fin n → ℝ) (ℓ : Fin n) (s : Bool), InCube x → FeasibleCoordDir x ℓ s →
      ∃ D : ℝ, HasRightDerivAt0
          (fun h => chainRem P (tParam P ε) (chainLength P ε) π (x + h • coordDir ℓ s)) D ∧
        |D| ≤ 12 * pairWeight P π * tParam P ε ^ 3) := by sorry

end LinearChoresCLS
