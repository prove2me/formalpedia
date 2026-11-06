-- Prove2me | Theorems.Thm_IntConeFPT_lemma_15
-- name    : IntConeFPT.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:29.442648+00:00
-- url     : https://prove2.me/theorems/f235eb40-c6c0-4af8-b100-ce78be9c9271
-- title:
--   Lemma 15 (Uniform Multiplicity Bound) — feasible, optimal and negative-cost homogeneous representations with total multiplicity $\le N_\star$
-- statement:
--   Let $I$ be a valid instance, $M\ge1$ an integer with $P^{(t)}\subseteq[-M,M]^{d+k}$ for all $t$, and $U\ge1$. Let $Wy_{\mathrm{agg}}\le c_{\mathrm{agg}}$ and $A^{(t)}x+B^{(t)}u\le b^{(t)}$ be an integral description of the instance bounded by $U$ (all entries and right-hand sides, and all coefficients $b_i-a_i^\top x$, $W_{i,y^{(t)}}x+W_{i,N^{(t)}}$ obtained by substituting integer $x\in[-M,M]^d$, have absolute value at most $U$). Let
--   $$
--   s=\tau2^d,\quad R=sk,\quad H=(R+1)!\,U^{R+1},\quad N_\star=s(s+1)\,s!\,H^s.\tag{3.4}
--   $$
--   Then:
--
--   1. if the instance is feasible, it has a feasible representation with $\sum_tN^{(t)}\le N_\star$;
--   2. if it is feasible and its objective is bounded below, it has an optimal representation (cost at most that of every feasible one) with $\sum_tN^{(t)}\le N_\star$;
--   3. if some representation (generators in the $S^{(t)}$, nonnegative integer multiplicities) satisfies $Wy_{\mathrm{agg}}\le0$ and has negative cost, then one with these properties has $\sum_tN^{(t)}\le N_\star$.
--
--   This removes the multiplicity bound (1.1) from Proposition 14 and bounds the search for an unboundedness certificate.
--
--   **Formalization Note** A representation is a multiplicity vector supported in the $S^{(t)}$; $y_{\mathrm{agg}}$ is the tuple $((y^{(t)},v^{(t)},N^{(t)}))_t$, and `IntDesc.Describes` / `IntDesc.BoundedBy` state that the integral systems describe the instance and are bounded by $U$.
--
--   Differences from the source:
--   - generalization: U: a computable integer bounding the coefficients after clearing denominators of the instance systems (p.17); M from (2.1) → every integer U ≥ 1, every integral description (W, c_agg), (A^(t), B^(t), b^(t)) of Q × A and of the P^(t), bounded by U in the paper's sense, and every M ≥ 1 with P^(t) ⊆ [−M, M]^{d+k}; reason: the cleared systems of the instance, with the paper's U and M, are one such choice
--   - encoding: R in (3.4) → Rk; reason: name clash with residue tuples
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
--   - reading: P^(1), …, P^(τ) (implicitly at least one type) → Instance.Valid requires 1 ≤ τ; reason: the paper lists τ types and its bounds contain log(τ + 1); there are no instances with τ = 0 in the source
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Lemma 15, p.17 (restated with proof, Section B.3, p.39); (3.4) and the definition of W, U on p.17

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation

open OnlineCRS.Combine

namespace IntConeFPT

/-- **Lemma 15 (Uniform Multiplicity Bound).**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Lemma 15, p.17 (restated with proof p.39): "Every feasible
instance has a feasible representation of total multiplicity at most N⋆. If its objective is
bounded below, it has an optimal representation with the same bound. Moreover, if W y_agg ≤ 0
admits a generator representation with integer multiplicities and negative cost, it admits one of
total multiplicity at most N⋆."

Here (§3.6, p.17) `W y_agg ≤ c_agg` combines the constraints of `Q` and `A`, the systems are
integral after clearing denominators, `U ≥ 1` bounds all their coefficients and right-hand sides,
including the coefficients obtained by substituting an integer vector `x ∈ [−M, M]^d` into a local
or aggregate constraint, and `N⋆ = s(s+1) s! H^s` with `s = τ2^d`, `R = sk`, `H = (R+1)! U^{R+1}`
((3.4)). The statement is made for **every** integer `M ≥ 1` with `P^(t) ⊆ [−M, M]^{d+k}`, every
integral description `(W, c_agg)`, `(A^(t), B^(t), b^(t))` of the instance's sets and every `U ≥ 1`
bounding it in this sense.

**Formalization Note.** A representation is a multiplicity vector supported in the `S^(t)`; its
total multiplicity is `Σ_t N^(t)`; "optimal" means cost at most that of every feasible
representation. -/
theorem lemma_15 (I : Instance) (hI : I.Valid) (M U : ℕ) (hM : 1 ≤ M)
    (hbox : ∀ t, ∀ p ∈ I.P t, InBox M p) (hU : 1 ≤ U) (D : IntDesc I) (hD : D.Describes)
    (hDU : D.BoundedBy M U) :
    ((∃ μ, I.Feasible μ) → ∃ μ, I.Feasible μ ∧ I.totalCount μ ≤ Nstar I.τ I.d I.k U) ∧
    ((∃ μ, I.Feasible μ) → (∃ L : ℝ, ∀ μ, I.Feasible μ → L ≤ I.cost μ) →
      ∃ μ, I.Feasible μ ∧ I.totalCount μ ≤ Nstar I.τ I.d I.k U ∧
        ∀ μ', I.Feasible μ' → I.cost μ ≤ I.cost μ') ∧
    ((∃ μ, I.Supported μ ∧ (∀ i, D.aggLHS (fun t => I.typeAgg μ t) i ≤ 0) ∧ I.cost μ < 0) →
      ∃ μ, I.Supported μ ∧ (∀ i, D.aggLHS (fun t => I.typeAgg μ t) i ≤ 0) ∧ I.cost μ < 0 ∧
        I.totalCount μ ≤ Nstar I.τ I.d I.k U) := by sorry

end IntConeFPT
