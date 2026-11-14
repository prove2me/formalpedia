-- Prove2me | Theorems.Thm_LinearChoresCLS_proposition_4_1
-- name    : LinearChoresCLS.proposition_4_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T21:47:35.437058+00:00
-- url     : https://prove2.me/theorems/aa51f759-5813-46f6-9c8c-57650d186537
-- title:
--   Proposition 4.1 — sufficient conditions for the reduction (analytic form)
-- statement:
--   Let $F$ be a valid linear chores market, let $Q(x)=\frac12x^\top Ax+c^\top x$ be the quadratic of an instance with $\varepsilon>0$, and let $p:[0,1]^n\to\mathcal P$ be a price mapping into the price domain of $F$ such that:
--
--   1. (a)(ii) for every $x\in[0,1]^n$ and every feasible coordinate direction $\tilde v$ at $x$, the curve $h\mapsto p(x+h\tilde v)$ has a finite right derivative at $h=0$;
--   2. (b) there are $\alpha>0$, $C\in\mathbb R$, a function $R:[0,1]^n\to\mathbb R$ and $0\le\beta\le\alpha\varepsilon$ with
--   $$
--   \Psi(p(x))=C+\alpha Q(x)+R(x)\quad (x\in[0,1]^n),\qquad |R(x+he_i)-R(x)|\le\beta|h|
--   $$
--   for every $i$ and every coordinate segment from $x$ to $x+he_i$ contained in $[0,1]^n$.
--
--   Then every $x^\star\in[0,1]^n$ such that $p(x^\star)$ is an equilibrium price vector of $F$ is an $\varepsilon$-KKT point of the instance.
--
--   With the decoder of item (a)(i), whose output $x^\star=g(I,(p^\star,z^\star))$ satisfies $p(x^\star)=p^\star$, this gives the printed conclusion: an $\varepsilon$-KKT point is recovered in polynomial time from any exact rational equilibrium.
--
--   **Formalization Note** The coordinate segments allow $h$ of either sign. The polynomial-time content of item (a)(i) and of the conclusion is carried by `LinearChoresCLS.reduction_figure_1`.
--
--   Differences from the source:
--   - generalization: F = f(I), the market constructed from I, with strictly positive rational data → any valid chores market F with real data; reason: the argument (p.12) uses only validity of F; it specializes to f(I)
--   - generalization: (a)(i): a polynomial-time decoder g with p(g(I,(p⋆,z⋆))) = p⋆ for every exact rational equilibrium; conclusion: an ε-KKT point can be recovered in polynomial time → no decoder hypothesis; conclusion: every x⋆ ∈ [0,1]ⁿ with p(x⋆) an equilibrium price vector is ε-KKT; reason: the decoder's output is such an x⋆, so (a)(i) plus this statement gives the printed conclusion; the polynomial-time part is the reduction milestone
--   - generalization: rational ε > 0 → real ε > 0; reason: rational ε is a special case
--   - generalization: QP dimension n ≥ 1 (A ∈ ℚ^{n×n}, [n] for positive n, p.5) → any n : ℕ; reason: at n = 0 the box is one point and every clause holds trivially; n ≥ 1 is a special case
--   - encoding: p : [0,1]ⁿ → P and R : [0,1]ⁿ → ℝ → pm, R : (Fin n → ℝ) → …, with pm x ∈ P and the identity Φ = C + αQ + R required only for x ∈ [0,1]ⁿ; reason: values off the box are never used (feasible directions stay in the box for small h > 0); every map on the box extends
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Proposition 4.1, pp.11–12

import Mathlib
import Definitions.Def_LinearChoresCLS_Psi
import Definitions.Def_LinearChoresCLS_RightDeriv
import Definitions.Def_LinearChoresCLS_EpsKKT

open Finset NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **Proposition 4.1 (sufficient conditions for the reduction)** (arXiv:2611.06589, held version
sha256 85d34a9e…, pp.11–12), in analytic form. Let `F` be a valid linear chores market, `Q` the
quadratic of an instance `(A, c, ε)` with `ε > 0`, and `p : [0,1]ⁿ → P` a price mapping such that
(a)(ii) for every `x ∈ [0,1]ⁿ` and every feasible coordinate direction `ṽ` at `x`, `h ↦ p(x + hṽ)`
has a finite right derivative at `h = 0`; and (b) there are `α > 0`, `C`, `R : [0,1]ⁿ → ℝ` and
`0 ≤ β ≤ αε` with `Ψ(p(x)) = C + αQ(x) + R(x)` on `[0,1]ⁿ` and `|R(x + heᵢ) − R(x)| ≤ β|h|` on every
coordinate segment in `[0,1]ⁿ`. Then every `x⋆ ∈ [0,1]ⁿ` such that `p(x⋆)` is an equilibrium price
vector of `F` is an ε-KKT point of the instance.

**Formalization Note.** With the decoder of (a)(i), whose output `x⋆ = g(I, (p⋆, z⋆))` satisfies
`p(x⋆) = p⋆`, this gives the printed conclusion "we can recover an ε-KKT point of `I` in polynomial
time from any exact rational equilibrium". The polynomial-time part is the reduction
`LinearChoresCLS.reduction_figure_1`. -/
theorem proposition_4_1 {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]
    (F : ChoresMarket N M) (hF : F.Valid) {n : ℕ} (P : Quadratic n) (ε : ℝ) (hε : 0 < ε)
    (pm : (Fin n → ℝ) → (M → ℝ)) (hdom : ∀ x, InCube x → pm x ∈ F.priceDomain)
    (hderiv : ∀ x, InCube x → ∀ (i : Fin n) (s : Bool), FeasibleCoordDir x i s →
      ∃ D : M → ℝ, HasRightDerivAt0 (fun h => pm (x + h • coordDir i s)) D)
    (herr : ∃ (α C β : ℝ) (R : (Fin n → ℝ) → ℝ), 0 < α ∧
      (∀ x, InCube x → F.Psi (pm x) = C + α * quadraticValue P x + R x) ∧
      0 ≤ β ∧ β ≤ α * ε ∧
      ∀ (x : Fin n → ℝ) (i : Fin n) (h : ℝ), InCube x → InCube (x + h • Pi.single i (1 : ℝ)) →
        |R (x + h • Pi.single i (1 : ℝ)) - R x| ≤ β * |h|) :
    ∀ x, InCube x → (∃ z : N → M → ℝ, F.IsCE (pm x) z) → IsEpsKKT P ε x := by sorry

end LinearChoresCLS
