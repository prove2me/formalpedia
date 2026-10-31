-- Prove2me | Theorems.Thm_OnlineGND_theorem_6
-- name    : OnlineGND.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:43.820449+00:00
-- url     : https://prove2.me/theorems/f62a97ae-50dd-4e83-9a33-901b223e7dd1
-- title:
--   Theorem 6 — with a τ-approximate oracle, $L\le2\tau\,\mathrm{OPT}$ and $H\le2(e\alpha\tau)^\alpha\,\mathrm{OPT}$
-- statement:
--   Consider GND with weighted power costs $c_ex^{\alpha_e}$ ($c_e\ge0$, $\alpha_e\ge1$), weights $w_{i,e}\ge1$, $\alpha=\max_e\alpha_e$, $E_1=\{e:\alpha_e=1\}$, and a $\tau$-approximate min-cost oracle ($\tau\ge1$). Run the online algorithm (20) with $\rho=(e\tau\alpha)^{\alpha-1}$, and let $A$ be its final loads, $L=\sum_{e\in E_1}c_eA_e$ and $H=\sum_{e\in E\setminus E_1}c_eA_e^{\alpha_e}$. Then:
--
--   1. the algorithm chooses a reply in $\mathcal P_i$ for every request $i$;
--   2. it is $2(e\alpha\tau)^\alpha$-competitive: $L+H\le2(e\alpha\tau)^\alpha\cdot\mathrm{OPT}$;
--   3. $L\le2\tau\cdot\mathrm{OPT}$;
--   4. $H\le2(e\alpha\tau)^\alpha\cdot\mathrm{OPT}$;
--   5. $\dfrac L\tau+\dfrac H{(e\tau\alpha)^\alpha}\le2\cdot\mathrm{OPT}$.
--
--   Each bound holds with $\mathrm{OPT}$ replaced by the cost $\sum_ec_e(\ell^*_e)^{\alpha_e}$ of any solution $p^*$.
--
--   The separate bound on the linear part $L$, with factor $2\tau$ instead of $2(e\alpha\tau)^\alpha$, is what §5 needs to obtain the additive form $\max\{q,1\}\tau+(e\tau\alpha)^\alpha$ in Theorem 1.
--
--   Differences from the source:
--   - generalization: the three printed bounds → the same bounds plus clause 5, the combined bound proved on p.14, and clause 1; reason: extra conclusions; dropping them gives the printed theorem
--   - encoding: "there is a polynomial time online algorithm" and OPT → the algorithm (20) with $\rho=(e\tau\alpha)^{\alpha-1}$, a deterministic online recursion making one oracle call per request, compared against every solution; reason: the paper's own algorithm; the running time is carried by the shape of the definition, and OPT is the minimum over solutions
--   - encoding: $\alpha=\max_e\alpha_e$ → $\max(1,\max_e\alpha_e)$; reason: equal for $E\ne\emptyset$ since $\alpha_e\ge1$
--   - encoding: a $\tau$-approximation algorithm → $\tau\ge1$ and the oracle predicate on the instance's requests; reason: an approximation factor of a minimization problem is at least $1$
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, Theorem 6, p.12; proof pp.12–14 (ρ and the combined bound p.14)

import Definitions.Def_OnlineGND_Doubled

namespace OnlineGND

/-- **Theorem 6** (Nagarajan & Wang, arXiv:2007.07721v1, §4.1, p.12; proof pp.12–14). For GND with
weighted power costs `cₑ x^{αₑ}` and a `τ`-approximate min-cost oracle, the online algorithm (20)
with `ρ = (eτα)^{α−1}` chooses a reply in each `𝒫ᵢ`, is `2(eατ)^α`-competitive, and with
`L = Σ_{e∈E₁} cₑAₑ`, `H = Σ_{e∈E∖E₁} cₑAₑ^{αₑ}`:
`L ≤ 2τ · OPT`, `H ≤ 2(eατ)^α · OPT`, and (p.14) `L/τ + H/(eτα)^α ≤ 2 · OPT`.
Each bound is against the cost of every reply profile.

**Formalization Note.** `α = alphaMax α`, `E₁ = {e : αₑ = 1}`. The algorithm's cost is `L + H`. -/
theorem theorem_6 {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ} (c α : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hα : ∀ e, 1 ≤ α e) (reqs : Fin N → Request E)
    (hw : ∀ i e, 1 ≤ (reqs i).w e) (τ : ℝ) (hτ : 1 ≤ τ) (O : Request E → (E → ℝ) → Finset E)
    (hO : IsApproxOracle τ reqs O) (sol : Fin N → Finset E) (hsol : IsReplyProfile reqs sol) :
    IsReplyProfile reqs (powerAlg c α (rhoStar τ α) O reqs) ∧
    costL c α (load reqs (powerAlg c α (rhoStar τ α) O reqs))
        + costH c α (load reqs (powerAlg c α (rhoStar τ α) O reqs)) ≤
      2 * (Real.exp 1 * alphaMax α * τ) ^ alphaMax α * powerCost c α (load reqs sol) ∧
    costL c α (load reqs (powerAlg c α (rhoStar τ α) O reqs)) ≤
      2 * τ * powerCost c α (load reqs sol) ∧
    costH c α (load reqs (powerAlg c α (rhoStar τ α) O reqs)) ≤
      2 * (Real.exp 1 * alphaMax α * τ) ^ alphaMax α * powerCost c α (load reqs sol) ∧
    costL c α (load reqs (powerAlg c α (rhoStar τ α) O reqs)) / τ
        + costH c α (load reqs (powerAlg c α (rhoStar τ α) O reqs))
          / (Real.exp 1 * τ * alphaMax α) ^ alphaMax α ≤
      2 * powerCost c α (load reqs sol) := by sorry

end OnlineGND
