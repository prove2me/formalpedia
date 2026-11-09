-- Prove2me | Theorems.Thm_LinearChoresCLS_theorem_2_3
-- name    : LinearChoresCLS.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:47:43.975865+00:00
-- url     : https://prove2.me/theorems/b94a5f84-6667-4102-b1bc-5ab68ebbded6
-- title:
--   Theorem 2.3 — first-order characterization of equilibrium prices
-- statement:
--   Let $F$ be a linear Fisher market with chores with supplies $S_j>0$, earning requirements $B_a>0$ and disutilities $d_{aj}>0$, at least one chore, and let
--   $$
--   \mu_a(p)=\max_{j}\frac{p_j}{d_{aj}},\qquad \Psi(p)=-\sum_aB_a\log\mu_a(p).
--   $$
--   For every $p^\star$ in the price domain $\mathcal P$ the following are equivalent:
--
--   1. there is an allocation $z^\star$ such that $(p^\star,z^\star)$ is a competitive equilibrium;
--   2. for every $v\in\mathbb R^M$ with $\sum_jS_jv_j=0$ the right directional derivative
--   $$
--   \Psi'(p^\star;v)=\lim_{h\downarrow0}\frac{\Psi(p^\star+hv)-\Psi(p^\star)}{h}
--   $$
--   exists and satisfies $\Psi'(p^\star;v)\le0$.
--
--   The theorem turns equilibrium conditions into first-order conditions of a nonconvex program over $\mathcal P$; the reduction transfers these to approximate KKT conditions of the target quadratic.
--
--   **Formalization Note** "$\Psi'(p^\star;v)\le0$" is written "the right limit exists and is $\le 0$"; the paper defines $\Psi'$ whenever the limit exists, and at $p^\star>0$ it always does.
--
--   Differences from the source:
--   - encoding: Ψ′(p⋆; v) ≤ 0 → ∃ D, the right limit of (Ψ(p⋆ + h v) − Ψ(p⋆))/h is D and D ≤ 0; reason: the paper's Ψ′ is defined whenever the right-hand limit exists, and at p⋆ > 0 it always exists
--   - encoding: m ≥ 1 chores, positive data → [Nonempty M] and ChoresMarket.Valid; reason: the paper's standing assumptions of Section 2
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Theorem 2.3, Eqs. (2.3)–(2.4), p.7 (proof Appendix A, pp.44–45)

import Mathlib
import Definitions.Def_LinearChoresCLS_Psi
import Definitions.Def_LinearChoresCLS_RightDeriv

open Finset

namespace LinearChoresCLS

/-- **Theorem 2.3 (First-order characterization of equilibrium price)** (arXiv:2611.06589, held
version sha256 85d34a9e…, p.7). Let `F` be a linear Fisher market with chores, with supplies
`S_j > 0`, earning requirements `B_a > 0` and disutilities `d_{aj} > 0`, and let
`Ψ(p) = −∑_a B_a log μ_a(p)`, `μ_a(p) = max_j p_j/d_{aj}`. For every `p⋆ ∈ P` the following are
equivalent: (1) some allocation `z⋆` makes `(p⋆, z⋆)` a competitive equilibrium; (2) for every
`v ∈ ℝ^m` with `∑_j S_j v_j = 0`, the right directional derivative `Ψ′(p⋆; v)` exists and is `≤ 0`.

**Formalization Note.** "`Ψ′(p⋆; v) ≤ 0`" is stated as "the right limit exists and is `≤ 0`"; the
paper defines `Ψ′` whenever the right-hand limit exists, and at `p⋆ > 0` it always does. `m ≥ 1` is
`[Nonempty M]`. -/
theorem theorem_2_3 {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]
    (F : ChoresMarket N M) (hF : F.Valid) (pstar : M → ℝ) (hp : pstar ∈ F.priceDomain) :
    (∃ z : N → M → ℝ, F.IsCE pstar z) ↔
      ∀ v : M → ℝ, ∑ j, F.supply j * v j = 0 →
        ∃ D : ℝ, HasRightDerivAt0 (fun h => F.Psi (pstar + h • v)) D ∧ D ≤ 0 := by sorry

end LinearChoresCLS
