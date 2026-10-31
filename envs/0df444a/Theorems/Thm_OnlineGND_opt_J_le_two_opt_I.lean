-- Prove2me | Theorems.Thm_OnlineGND_opt_J_le_two_opt_I
-- name    : OnlineGND.opt_J_le_two_opt_I
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:39.405131+00:00
-- url     : https://prove2.me/theorems/5567d792-b89f-4ce1-8eff-fccb41362e30
-- title:
--   §5, p.14 — $\mathrm{OPT}_{\mathcal J}\le2\cdot\mathrm{OPT}_{\mathcal I}$
-- statement:
--   Let $\mathcal I$ be a GND instance with (D)oS costs ($\sigma_e\ge0$, $\xi_e>0$, $\alpha_e\ge1$) and weights $w_{i,e}\ge1$, and let $\mathcal J$ be the power-cost instance of §5, with copies $e_1,e_a$ of each resource, $c_{e_1}=\xi_eq_e^{\alpha_e-1}$, $\alpha_{e_1}=1$, $c_{e_a}=\xi_e$, $\alpha_{e_a}=\alpha_e$. For every solution $p^*$ of $\mathcal I$ with loads $\ell^*$, the reply profile of $\mathcal J$ that uses both copies of each resource of $p^*_i$ is a solution of $\mathcal J$, and its cost satisfies
--   $$\sum_{r\in E'}c_r\,\ell_r^{\alpha_r}=\sum_{e\in E}h_e(\ell^*_e)\ \le\ 2\sum_{e\in E}f_e(\ell^*_e).$$
--   Hence $\mathrm{OPT}_{\mathcal J}\le2\cdot\mathrm{OPT}_{\mathcal I}$.
--
--   The bound transfers Theorem 6 on $\mathcal J$ back to the original instance.
--
--   Differences from the source:
--   - encoding: $\mathrm{OPT}_{\mathcal J}\le2\cdot\mathrm{OPT}_{\mathcal I}$ → every solution of $\mathcal I$ lifts to a solution of $\mathcal J$ of at most twice its cost; reason: equivalent, since OPT is the minimum over finitely many solutions
--   - encoding: $\xi_e\ge0$ → $\xi_e>0$; reason: $q_e$, used in $c_{e_1}$, is undefined at $\xi_e=0$
--   - encoding: resources $E'=E_1\cup E_a$ → $E\times\{\text{false},\text{true}\}$; reason: a labelling of the copies
--   - encoding: $q_e^{\alpha_e-1}$ in $c_{e_1}$ at $q_e=0$, $\alpha_e=1$ → the value $1$ (`Real.rpow`); reason: Lean convention $0^0=1$, the limit of $q_e^0$ as $q_e\to0$; it changes no instance with $q_e>0$ or $\alpha_e>1$
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, §5, p.14

import Definitions.Def_OnlineGND_Doubled

namespace OnlineGND

/-- **`OPT_𝒥 ≤ 2 · OPT_𝓘`** (Nagarajan & Wang, arXiv:2007.07721v1, §5, p.14, from the first inequality
of Lemma 1): every reply profile `p*` of the (D)oS instance `𝓘` (weights `≥ 1`) lifts to a reply
profile of the power-cost instance 𝒥 whose cost `Σ_{r∈E′} c_r (ℓ_r)^{α_r} = Σₑ hₑ(ℓ*ₑ)` is at most
`2 Σₑ fₑ(ℓ*ₑ)`.

**Formalization Note.** `𝒥` has resources `E × Bool`, requests `liftReq (reqs i)`, scalars `cJ` and
exponents `alphaJ`. The minimum over profiles is stated profile by profile. -/
theorem opt_J_le_two_opt_I {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ} (σ ξ α : E → ℝ)
    (hσ : ∀ e, 0 ≤ σ e) (hξ : ∀ e, 0 < ξ e) (hα : ∀ e, 1 ≤ α e) (reqs : Fin N → Request E)
    (hw : ∀ i e, 1 ≤ (reqs i).w e) (sol : Fin N → Finset E) (hsol : IsReplyProfile reqs sol) :
    IsReplyProfile (fun i => liftReq (reqs i)) (fun i => liftSet (sol i)) ∧
      powerCost (cJ σ ξ α) (alphaJ α)
          (load (fun i => liftReq (reqs i)) (fun i => liftSet (sol i))) ≤
        2 * ∑ e, dosCost σ ξ α e (load reqs sol e) := by sorry

end OnlineGND
