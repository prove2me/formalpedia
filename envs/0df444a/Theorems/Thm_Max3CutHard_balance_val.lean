-- Prove2me | Theorems.Thm_Max3CutHard_balance_val
-- name    : Max3CutHard.balance_val
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:47:57.126372+00:00
-- url     : https://prove2.me/theorems/805cfeee-a6bb-4358-90ca-22ff1911e337
-- title:
--   Section 2 — balancing a role-separated instance preserves its value
-- statement:
--   Let $\Phi$ be a role-separated instance of 3Lin($\mathbb Z_3$) on finite variable sets $U$, $W$ with weights $\lambda_e\ge0$ summing to $1$, and let $\Phi'$ be the instance obtained by replacing every $u\in U$ by three copies $u^{(0)},u^{(1)},u^{(2)}$ and every equation $e$ by the three equations $u_e^{(c)}+w_e+w'_e=t_e+c$ ($c\in\mathbb Z_3$), each of weight $\lambda_e/3$. Then:
--
--   1. the weights of $\Phi'$ are non-negative and sum to $1$;
--   2. $\Phi'$ is balanced: every type has weight exactly $1/3$;
--   3. for every assignment $\sigma$ of $\Phi$, the assignment $\sigma(u^{(c)})=\sigma(u)+c$, $\sigma(w)$ unchanged, satisfies the same weight: $\mathrm{val}_{\Phi'}=\mathrm{val}_\Phi(\sigma)$;
--   4. for every assignment $\tau$ of $\Phi'$,
--   $$\mathrm{val}_{\Phi'}(\tau)=\frac13\sum_{c\in\mathbb Z_3}\mathrm{val}_\Phi(\sigma_c),\qquad \sigma_c(u)=\tau(u^{(c)})-c,\quad \sigma_c(w)=\tau(w);$$
--   5. $\mathrm{val}(\Phi')=\mathrm{val}(\Phi)$.
--
--   This is how Håstad's instances are made balanced, which is the form in which Theorem 2.1 is used.
--
--   Differences from the source:
--   - encoding: val(Φ′) ≤ val(Φ), and the lift σ(u^(c)) = σ(u) + c satisfies the same weight → one clause val(Φ′) = val(Φ) next to the lift clause; reason: the two printed facts together are the equality; nothing is added
--   - encoding: copies u^(0), u^(1), u^(2); role separation of Φ′ → pairs (u, c) : U × ZMod 3; separate types U × ZMod 3 and W; reason: Lean convention; same instances
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Håstad's equations, p.4

import Mathlib
import Definitions.Def_Max3CutHard_WInst_balance
import Definitions.Def_Max3CutHard_WInst_val
import Definitions.Def_Max3CutHard_WInst_IsWeighting
import Definitions.Def_Max3CutHard_WInst_Balanced

namespace Max3CutHard

/-- **Balancing Håstad's instances.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Håstad's equations, p.4: "To balance the
types, replace every `u ∈ U` by three copies `u^(0), u^(1), u^(2)` and each equation `e` by the
three equations `u_e^(c) + w_e + w′_e = t_e + c` (`c ∈ ℤ₃`), each of weight `λ_e/3`. The new
instance `Φ′` is role-separated (with `U × ℤ₃` and `W`), and every type has weight exactly `1/3`.
An assignment `σ` of `Φ` yields `σ(u^(c)) = σ(u) + c`, which satisfies the same weight.
Conversely, for any assignment `τ` of `Φ′`, `val_Φ′(τ) = (1/3) Σ_{c∈ℤ₃} val_Φ(σ_c)`,
`σ_c(u) = τ(u^(c)) − c`, `σ_c(w) = τ(w)`, and each `σ_c` is an assignment of `Φ` (the values on `W`
are shared), so `val(Φ′) ≤ val(Φ)`."

**Formalization Note.** Role separation of `Φ′` holds by its type `WInst (U × ℤ₃) W`. The five
clauses are: `Φ′` is a weighting; `Φ′` is balanced; the lift of `σ` satisfies the same weight;
the averaging identity; and `val(Φ′) = val(Φ)` (the printed `≤` together with the lift). -/
theorem balance_val {U W : Type} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (Φ : WInst U W) (hΦ : Φ.IsWeighting) :
    Φ.balance.IsWeighting ∧ Φ.balance.Balanced ∧
    (∀ (σU : U → ZMod 3) (σW : W → ZMod 3),
      Φ.balance.valAt (fun uc => σU uc.1 + uc.2) σW = Φ.valAt σU σW) ∧
    (∀ (τU : U × ZMod 3 → ZMod 3) (τW : W → ZMod 3),
      Φ.balance.valAt τU τW = (1 / 3) * ∑ c : ZMod 3, Φ.valAt (fun u => τU (u, c) - c) τW) ∧
    Φ.balance.val = Φ.val := by sorry

end Max3CutHard
