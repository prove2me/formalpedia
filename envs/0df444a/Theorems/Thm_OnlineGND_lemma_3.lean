-- Prove2me | Theorems.Thm_OnlineGND_lemma_3
-- name    : OnlineGND.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:56.468386+00:00
-- url     : https://prove2.me/theorems/c51951a1-89e0-41c8-8391-e4e3a544b7c0
-- title:
--   Lemma 3 — the relaxation with linear terms has value at most $(1+\alpha e^{-\alpha})\,\mathrm{OPT}$
-- statement:
--   Consider GND with weighted power costs $c_ex^{\alpha_e}$ ($c_e\ge0$, $\alpha_e\ge1$), weights $w_{i,e}\ge1$, and $\alpha=\max_e\alpha_e$. Let $S\subseteq E$. For every solution $p^*$ (a reply $p^*_i\in\mathcal P_i$ for each $i$, with loads $\ell^*$) there is a feasible solution $x$ of (P) with
--   $$\sum_{e\in E}c_e\Bigl(\sum_iw_{i,e}\!\!\sum_{p\in\mathcal P_i:e\in p}\!\!x_{i,p}\Bigr)^{\alpha_e}+\sum_{e\in S}\frac{c_e\alpha_e}{e^\alpha}\sum_iw_{i,e}^{\alpha_e}\!\!\sum_{p\in\mathcal P_i:e\in p}\!\!x_{i,p}\ \le\ (1+\alpha e^{-\alpha})\sum_ec_e(\ell^*_e)^{\alpha_e}.$$
--   Hence the optimal value of this convex program is at most $(1+\alpha e^{-\alpha})\cdot\mathrm{OPT}$.
--
--   With $S=E$ this is Lemma 3 for the objective (12); with $S=E\setminus E_1$ it is the bound for (21) used in the proof of Theorem 6.
--
--   **Formalization Note** $\alpha$ is $\max(1,\max_e\alpha_e)$ and $e^{-\alpha}$ is `Real.exp (-α)`.
--
--   Differences from the source:
--   - generalization: linear terms on all of $E$ (objective (12)) → on an arbitrary $S\subseteq E$; reason: $S=E$ is the printed lemma and $S=E\setminus E_1$ is objective (21), to which Theorem 6 applies it ("As in Lemma 3", p.13)
--   - encoding: optimal value of the program $\le(1+\alpha e^{-\alpha})\,\mathrm{OPT}$ → for every reply profile some feasible $x$ has objective $\le(1+\alpha e^{-\alpha})$ times the profile's cost; reason: equivalent to the printed form since the optimal value is at most every feasible objective and OPT is attained by a profile
--   - encoding: $\alpha=\max_e\alpha_e$ → $\max(1,\max_e\alpha_e)$; reason: equal for $E\ne\emptyset$ since $\alpha_e\ge1$
--   - encoding: $x\ge0$ → $x_{i,p}\ge0$ for $p\in\mathcal P_i$; reason: only these variables exist in (P)
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, Lemma 3, p.10; (12) p.10; (21) and its use p.12–13

import Definitions.Def_OnlineGND_Relaxation
import Definitions.Def_OnlineGND_PowerAlg

namespace OnlineGND

/-- **Lemma 3** (Nagarajan & Wang, arXiv:2007.07721v1, §4, p.10), with the linear terms on any
`S ⊆ E`: the optimal value of the convex program with the constraints of (P) and objective
`Σ_{e∈E} cₑ(Σᵢ w_{i,e} Σ_{p:e∈p} x_{i,p})^{αₑ} + Σ_{e∈S} (cₑαₑ/e^α) Σᵢ w_{i,e}^{αₑ} Σ_{p:e∈p} x_{i,p}`
is at most `(1 + α e^{−α}) · OPT`. Here: for every reply profile `p*` there is a feasible `x` whose
objective is at most `(1 + α e^{−α}) · Σₑ cₑ (ℓ*ₑ)^{αₑ}`.

**Formalization Note.** `S = E` is the printed objective (12); `S = E ∖ E₁` is (21), the form used in
Theorem 6 ("As in Lemma 3", p.13). `α = alphaMax α`. "Optimal value ≤ C · OPT" is stated profile by
profile, with the minimum of the relaxation witnessed by a feasible point. -/
theorem lemma_3 {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ} (c α : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hα : ∀ e, 1 ≤ α e) (S : Finset E) (reqs : Fin N → Request E)
    (hw : ∀ i e, 1 ≤ (reqs i).w e) (sol : Fin N → Finset E) (hsol : IsReplyProfile reqs sol) :
    ∃ x : Fin N → Finset E → ℝ, IsPrimalFeasible reqs x ∧
      relaxObj c α S reqs x ≤
        (1 + alphaMax α * Real.exp (-alphaMax α)) * powerCost c α (load reqs sol) := by sorry

end OnlineGND
