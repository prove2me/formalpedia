-- Prove2me | Theorems.Thm_FracTruthSched_claim_1
-- name    : FracTruthSched.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:31:37.738316+00:00
-- url     : https://prove2.me/theorems/dbb6a4fb-3039-4562-8e09-f0e51dec8841
-- title:
--   Claim 1 — the symmetrized mechanism is truthful and relabelling-equivariant
-- statement:
--   Let $(\hat x,\hat P)$ be a feasible truthful fractional mechanism on $n$ machines and $m$ tasks (on nonnegative inputs), and let $G$ be a group of permutations of the $m$ tasks. Let $(\bar x,\bar P)$ be its symmetrization over $G$. Then:
--
--   1. $(\bar x,\bar P)$ is feasible and truthful;
--   2. for every $\gamma\in G$, every input $s$, every machine $i$ and every task $e$,
--   $$\bar x_{ie}(\gamma s)=\bar x_{i,\gamma(e)}(s)\qquad\text{and}\qquad \bar P_i(\gamma s)=\bar P_i(s),$$
--   where $(\gamma s)_{ie}=s_{i,\gamma(e)}$.
--
--   Averaging a mechanism over task relabellings preserves truthfulness and makes it symmetric. In the padding construction this gives property (iv) and lets identical tasks receive identical fractions.
--
--   Differences from the source:
--   - generalization: the mechanism R_m and the group Π_κ of permutations of the tasks of the padded instance (t, κ) mapping every edge to a parallel edge and fixing every self-loop → any feasible truthful mechanism on m tasks and any subgroup G of the permutations of Fin m; reason: Π_κ is a subgroup and the proof uses only the group property (π′ = γ ∘ π ranges over the group); specializes to the source's claim
--   - generalization: the symmetrized mechanism is truthful → it is feasible and truthful; reason: an extra, true clause (an average of fractional allocations is a fractional allocation); the source's conclusion is contained in it
--   - generalization: the identities for every input s → the identities for every real matrix s, not only nonnegative ones; reason: the identities are algebraic; the nonnegative case is a specialization
--   - encoding: a deterministic fractional mechanism on nonnegative inputs: x_ij(t) ∈ [0,1], Σ_i x_ij(t) = 1, payments P_i(t), truthfulness (1) for nonnegative true types, reports and opposing reports → FracMech n τ (total functions x, P on real matrices) with IsFeasibleOn and IsTruthfulOn imposed on the admissible inputs only (Nonneg, resp. IsGraphInput); values elsewhere are unconstrained; reason: Lean convention; the paper's mechanisms are exactly the restrictions of such pairs to the admissible inputs
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Claim 1, App. A, p.23

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_symmetrize

set_option autoImplicit false

namespace FracTruthSched

/-- **Claim 1 (Symmetrized mechanism)** (Anastasiadis et al., *Tight bounds for fractional and
randomized truthful scheduling*, arXiv:2611.06642v1, Claim 1, App. A, p.23). The symmetrized
mechanism `(x̄, P̄)` of a truthful fractional mechanism `(x̂, P̂)` is truthful, and for every `γ ∈ G`
and every input `s`, `x̄_ie(γs) = x̄_{i,γ(e)}(s)` and `P̄_i(γs) = P̄_i(s)`.

**Formalization Note.** Stated for any feasible truthful fractional mechanism on `m` tasks (on
nonnegative inputs) and any subgroup `G` of the task permutations; the paper's `Π_κ` (permutations of
the tasks of `(t, κ)` mapping every edge to a parallel edge and fixing every self-loop) is one such
subgroup. The conclusion also records feasibility of `(x̄, P̄)`. `(γs)_ie = s_{i,γ(e)}` is `relabel γ s`;
the identities are stated at every input `s`. -/
theorem claim_1 {n m : ℕ} (M : FracMech n (Fin m)) (hfeas : IsFeasibleOn Nonneg M)
    (htruth : IsTruthfulOn Nonneg M) (G : Subgroup (Equiv.Perm (Fin m))) :
    IsFeasibleOn Nonneg (symmetrize M G) ∧ IsTruthfulOn Nonneg (symmetrize M G) ∧
      ∀ γ ∈ G, ∀ (s : Fin n → Fin m → ℝ) (i : Fin n) (e : Fin m),
        (symmetrize M G).x (relabel γ s) i e = (symmetrize M G).x s i (γ e) ∧
          (symmetrize M G).P (relabel γ s) i = (symmetrize M G).P s i := by sorry

end FracTruthSched
