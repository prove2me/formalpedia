-- Prove2me | Theorems.Thm_OnlineGND_theorem_1
-- name    : OnlineGND.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:51.960684+00:00
-- url     : https://prove2.me/theorems/7f4e31ce-1174-4aaf-8982-18c42b768873
-- title:
--   Theorem 1 — the online algorithm for GND with (D)oS costs is $4(\max\{q,1\}\tau+(e\tau\alpha)^\alpha)$-competitive
-- statement:
--   Let $E$ be a finite set of resources, each with a (D)oS cost
--   $$f_e(x)=\begin{cases}0&x=0,\\ \sigma_e+\xi_ex^{\alpha_e}&x>0,\end{cases}\qquad\sigma_e\ge0,\ \xi_e>0,\ \alpha_e\ge1,$$
--   let $q_e=(\sigma_e/\xi_e)^{1/\alpha_e}$, $q=\max_eq_e$ and $\alpha=\max_e\alpha_e$. Let $N$ requests arrive online, request $i$ with reply collection $\mathcal P_i$ and weights $w_{i,e}\ge1$, and let $O$ be a $\tau$-approximate min-cost oracle ($\tau\ge1$). The online algorithm of §5 runs the algorithm of Theorem 6 with $\rho=(e\tau\alpha)^{\alpha-1}$ on the power-cost instance $\mathcal J$ (two copies $e_1,e_a$ of each resource, $c_{e_1}=\xi_eq_e^{\alpha_e-1}$, $c_{e_a}=\xi_e$), with the oracle of $\mathcal J$ obtained from $O$. Then:
--
--   1. the algorithm chooses a reply in $\mathcal P_i$ for every request $i$;
--   2. its final loads $A$ satisfy, for every solution $p^*$ with loads $\ell^*$,
--   $$\sum_{e\in E}f_e(A_e)\ \le\ 4\bigl(\max\{q,1\}\,\tau+(e\tau\alpha)^\alpha\bigr)\sum_{e\in E}f_e(\ell^*_e).$$
--
--   Here $e\approx2.718$ is Euler's number. Since $\tau\le(e\alpha\tau)^\alpha$ and $\max\{q,1\}\le q+1$, the ratio is $O(q\tau+(e\alpha\tau)^\alpha)$, the competitive ratio of Theorem 1. The algorithm is deterministic and online, and it makes one oracle call per request.
--
--   **Formalization Note** $\alpha$ and $\max\{q,1\}$ are computed as $\max(1,\max_e\alpha_e)$ and $\max(1,\max_eq_e)$. The resources of $\mathcal J$ are $E\times\{\text{false},\text{true}\}$; since both copies of $e$ carry the load of $e$, the run on $\mathcal J$ is computed on $E$ directly.
--
--   Differences from the source:
--   - reading: "there is a polynomial time $O(q\tau+(e\alpha\tau)^\alpha)$-competitive deterministic online algorithm" → the paper's own algorithm (§5) with the constant $4(\max\{q,1\}\tau+(e\tau\alpha)^\alpha)$ of (27); reason: the explicit constant implies the $O(\cdot)$ bound, so this is the stronger reading
--   - generalization: the bound on the cost → the same bound plus clause 1, that every reply lies in $\mathcal P_i$; reason: an extra conclusion; dropping it gives the printed theorem
--   - encoding: polynomial time, deterministic, online → an online recursion that computes reply $i$ from requests $1,\dots,i$ with one oracle call and $|E|$ closed-form cost evaluations; reason: the running time is relative to the oracle (p.3) and the costs are real powers, which have no bit encoding
--   - encoding: competitive against OPT → against the cost of every solution; reason: OPT is the minimum over solutions
--   - encoding: $\xi_e\ge0$ → $\xi_e>0$; reason: $q_e=(\sigma_e/\xi_e)^{1/\alpha_e}$ is undefined at $\xi_e=0$
--   - encoding: a $\tau$-approximation algorithm → $\tau\ge1$ and the oracle predicate on the instance's requests; reason: an approximation factor of a minimization problem is at least $1$
--   - encoding: $\alpha=\max_e\alpha_e$, $\max\{q,1\}$ → $\max(1,\max_e\alpha_e)$, $\max(1,\max_eq_e)$; reason: equal for $E\ne\emptyset$ since $\alpha_e\ge1$
--   - encoding: Theorem 6's algorithm run on $\mathcal J$ with the lifted oracle → the same run computed on $E$, request $i$ receiving $O(i,d')$ with $d'_e=\bar\psi_{e_1}+\bar\psi_{e_a}$; reason: both copies of $e$ carry the load of $e$ and the replies of $\mathcal J$ are the lifts of those of $\mathcal I$ (p.15), so the replies are the same
--   - encoding: $q_e^{\alpha_e-1}$ in $c_{e_1}$ at $q_e=0$, $\alpha_e=1$ → the value $1$ (`Real.rpow`); reason: Lean convention $0^0=1$, the limit of $q_e^0$ as $q_e\to0$; it changes no instance with $q_e>0$ or $\alpha_e>1$
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, Theorem 1, p.3; proof §5, (25)–(27), p.14

import Definitions.Def_OnlineGND_Doubled

namespace OnlineGND

/-- **Theorem 1** (Nagarajan & Wang, arXiv:2007.07721v1, p.3; proof §5, p.14, with the constant of
(27)). For GND with (D)oS costs `fₑ` (1) and a `τ`-approximate min-cost oracle, the deterministic
online algorithm of §5 chooses a reply in each `𝒫ᵢ`, and its final loads `A` satisfy, for every
reply profile `p*` with loads `ℓ*`,
`Σₑ fₑ(Aₑ) ≤ 4 (max{q,1} τ + (eτα)^α) · Σₑ fₑ(ℓ*ₑ)`.
Since `τ ≤ (eατ)^α`, this gives the printed `O(qτ + (eατ)^α)`-competitive ratio.

**Formalization Note.** `σₑ ≥ 0`, `ξₑ > 0`, `αₑ ≥ 1`, `w_{i,e} ≥ 1`, `τ ≥ 1`;
`α = alphaMax α = max(1, maxₑ αₑ)`, `max{q,1} = qMax1 = max(1, maxₑ qₑ)`. The algorithm `dosAlg`
runs Theorem 6's algorithm (20) with `ρ = (eτα)^{α−1}` on the doubled instance 𝒥, with the lifted
oracle; it makes one oracle call per request. -/
theorem theorem_1 {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ} (σ ξ α : E → ℝ)
    (hσ : ∀ e, 0 ≤ σ e) (hξ : ∀ e, 0 < ξ e) (hα : ∀ e, 1 ≤ α e) (reqs : Fin N → Request E)
    (hw : ∀ i e, 1 ≤ (reqs i).w e) (τ : ℝ) (hτ : 1 ≤ τ) (O : Request E → (E → ℝ) → Finset E)
    (hO : IsApproxOracle τ reqs O) (sol : Fin N → Finset E) (hsol : IsReplyProfile reqs sol) :
    IsReplyProfile reqs (dosAlg σ ξ α τ O reqs) ∧
      ∑ e, dosCost σ ξ α e (load reqs (dosAlg σ ξ α τ O reqs) e) ≤
        4 * (qMax1 σ ξ α * τ + (Real.exp 1 * τ * alphaMax α) ^ alphaMax α) *
          ∑ e, dosCost σ ξ α e (load reqs sol e) := by sorry

end OnlineGND
