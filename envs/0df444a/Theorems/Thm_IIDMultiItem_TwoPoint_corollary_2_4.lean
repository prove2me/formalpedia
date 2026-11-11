-- Prove2me | Theorems.Thm_IIDMultiItem_TwoPoint_corollary_2_4
-- name    : IIDMultiItem.TwoPoint.corollary_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:57:22.069696+00:00
-- url     : https://prove2.me/theorems/57e2343f-7716-4c34-89d5-a34a4b0e79c0
-- title:
--   Corollary 2.4 (several buyers) — Rev(M) ≤ E_v ∑_j max{0, Φ_1j(v), …, Φ_nj(v)}, with a sufficient equality condition
-- statement:
--   Let $(T,f)$ be a type space with a prior and $M=(x,s)$ a feasible, DSIC, ex-post IR mechanism. Choose a flow $\lambda_{i,v_{-i}}$ for every buyer $i$ and reports $v_{-i}$ of the others, and let $\Phi_{ij}(v)$ be the virtual value of item $j$ at type $v_i$ under the flow chosen for $(i,v_{-i})$. Then
--   $$\mathrm{Rev}(M)\ \le\ \mathbb E_v\sum_{j=1}^m\max\{0,\Phi_{1j}(v),\dots,\Phi_{nj}(v)\}.\tag{2.9}$$
--   Equality holds if, for every $i$ and $v_{-i}$, every constraint of positive weight in the flow chosen for $(i,v_{-i})$ is tight, and $\sum_i\Phi_{ij}(v)x_{ij}(v)=\max\{0,\max_i\Phi_{ij}(v)\}$ for every $v$ and $j$.
--
--   The equality condition is only sufficient (an implication), as in the source.
--
--   Differences from the source:
--   - generalization: the type space supp(F)^m of a finite distribution F with product mass function f(t) = ∏_j f(t_j) → any finite type space Ts with a prior mass function (TypeSpace.IsPrior: f(t) > 0, ∑ f = 1) and arbitrary value vectors; reason: the identity and the bound use only the positivity of f; FinPrior.typeSpace F m satisfies IsPrior, so the statement specializes to the paper's, and the two-point type space of Section 3 is also an instance
--   - encoding: a flow chosen for every buyer i and reports v_{-i} → a family lam i v indexed by buyers and full profiles, with lam i (Function.update v i t) = lam i v; reason: the invariance says exactly that the flow depends on (i, v_{-i}) only; every choice of flows per (i, v_{-i}) is such a family
--   - encoding: max{0, Φ_1j(v), …, Φ_nj(v)} → posMax (fun i => Φ v i j); reason: the maximum of the finite set {0} ∪ {Φ_ij(v)}
--   - generalization: n ≥ 1 buyers (§2.1) → any n ∈ ℕ; reason: at n = 0 both sides of (2.9) are 0; for n ≥ 1 it is the paper's statement (m = 0 is already covered by the type-space generalization)
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), p. 12 (PDF 14), Corollary 2.4

import Mathlib
import Definitions.Def_IIDMultiItem_TwoPoint_Model
import Definitions.Def_IIDMultiItem_TwoPoint_Flow

open scoped BigOperators

namespace IIDMultiItem.TwoPoint

/-- Corollary 2.4 (several buyers). For a DSIC, ex-post IR mechanism and a flow `lam i v` chosen
for every buyer `i` and reports `v_{-i}` (it does not depend on `v i`), with
`Φ_ij(v)` the virtual value of item `j` at type `v_i` under the flow chosen for `(i, v_{-i})`:
`Rev(M) ≤ E_v ∑_j max{0, Φ_1j(v), …, Φ_nj(v)}` (2.9), with equality if every constraint of positive
weight in every chosen flow is tight and `∑_i Φ_ij(v) x_ij(v) = max{0, max_i Φ_ij(v)}`. -/
theorem corollary_2_4 {T : Type} [Fintype T] {n m : ℕ} (Ts : TypeSpace T m) (hTs : Ts.IsPrior)
    (M : Mechanism T n m) (hM : M.Feasible) (hIC : M.DSIC_IR Ts)
    (lam : Fin n → (Fin n → T) → Flow T) (hflow : ∀ i v, (lam i v).IsFlow Ts)
    (hothers : ∀ i v t, lam i (Function.update v i t) = lam i v) :
    let Φ : (Fin n → T) → Fin n → Fin m → ℝ := fun v i j => (lam i v).virtualValue Ts (v i) j
    M.Rev Ts ≤ ∑ v : Fin n → T, (∏ i, Ts.pmf (v i)) * ∑ j, posMax (fun i => Φ v i j) ∧
    ((∀ i v, M.TightOn Ts i v (lam i v)) →
      (∀ v j, ∑ i, Φ v i j * M.x v i j = posMax (fun i => Φ v i j)) →
      M.Rev Ts = ∑ v : Fin n → T, (∏ i, Ts.pmf (v i)) * ∑ j, posMax (fun i => Φ v i j)) := by sorry

end IIDMultiItem.TwoPoint
