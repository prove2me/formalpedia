-- Prove2me | Theorems.Thm_MenuCostPricing_eq_3_4
-- name    : MenuCostPricing.eq_3_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:36:01.549264+00:00
-- url     : https://prove2.me/theorems/53611cda-5dcb-4bf0-b6be-5ab8df83b58e
-- title:
--   (3)–(4) — constraints (3)–(4) imply budget feasibility, and every budget-feasible $x$ satisfies them with $\Gamma(x)$
-- statement:
--   Let $\Gamma\subseteq[2,T]$ be a set of periods. Consider the constraints
--   $$
--   C_{\mathrm{var}}(x)\le B-|\Gamma|\cdot f\quad(3),\qquad \Delta_{t-1,t}(x)=0\ \ \forall t\in[2,T]\setminus\Gamma\quad(4).
--   $$
--   1. Every pricing strategy satisfying (3) and (4) is budget-feasible: $C_{\mathrm{var}}(x)+C_{\mathrm{fixed}}(x)\le B$.
--   2. Every budget-feasible strategy $x$ satisfies (3) and (4) with $\Gamma=\Gamma(x)=\{t\in[2,T]:\Delta_{t-1,t}(x)>0\}$.
--
--   This replaces the coupled budget constraint by a variable-cost constraint and a constraint on where prices may change, once the change periods of the optimum are guessed.
--
--   Differences from the source:
--   - generalization: the optimal strategy x∗ satisfies (3)–(4) with Γ∗ → every budget-feasible x satisfies (3)–(4) with Γ(x); reason: the paper's observation uses only feasibility of x∗; specializes at x = x∗
--   - generalization: constraints (3)–(4) for Γ∗ → constraints (3)–(4) for every Γ ⊆ [2, T]; reason: the implication uses only |Γ| ≥ the number of change periods; specializes at Γ = Γ∗
--   - encoding: products i ∈ [n], levels ℓ ∈ [L], periods t ∈ [T]; Γ ⊆ [2, T]; a pricing strategy is a binary vector (xᵗ_{iℓ}) with one 1 per (t, i) → Fin n, Fin L, Fin T with Lean period t = paper period t + 1; Γ a Finset of Lean periods with 1 ≤ t.val; a strategy is a function Fin T → Fin n → Fin L; reason: Lean convention; the same instances and strategies
--   - reading: the model of §1.1 (p.2: "all prices are strictly positive"; products, price levels, MNL preference weights, menu costs, a number of customers with known finite support and oracle pmf) → Instance.Standing: n ≥ 1, L ≥ 1, p > 0, w ≥ 0, f ≥ 0, v ≥ 0, the support a duplicate-free list of ν ∈ ℕ with masses ≥ 0 summing to 1; reason: what the paper's words mean; only p > 0 is printed as a formula; B is any real
-- source:
--   Feldman & Segev, Dynamic Pricing with Menu Costs: Approximation Schemes and Applications to Grocery Retail, author manuscript (Mar 2025), §3.3, constraints (3)–(4), p.15

import Mathlib
import Definitions.Def_MenuCostPricing_Model
import Definitions.Def_MenuCostPricing_Proxy

namespace MenuCostPricing

/-- Feldman & Segev, author manuscript (Mar 2025), §3.3, constraints (3)–(4), p.15: "It is easy to
observe that any pricing strategy satisfying constraints (3) and (4) is budget-feasible, noting that
in particular, the optimal pricing strategy x∗ satisfies these two constraints."

1. For every set `Γ` of periods in `[2, T]` and every strategy `x` with (3) `Cvar(x) ≤ B − |Γ|·f` and
   (4) `∆_{t−1,t}(x) = 0` for all `t ∉ Γ`, `x` is budget-feasible.
2. Every budget-feasible `x` satisfies (3)–(4) with `Γ = Γ(x) = {t ∈ [2, T] : ∆_{t−1,t}(x) > 0}`.

**Formalization Note.** Part 2 is stated for every budget-feasible `x`, of which the optimum `x∗` is
one. Periods are 0-based: `Γ` is a set of Lean periods with `1 ≤ t.val`. -/
theorem eq_3_4 {n L T : ℕ} (I : Instance n L T) (hI : I.Standing) :
    (∀ Γ : Finset (Fin T), (∀ t ∈ Γ, 1 ≤ t.val) → ∀ x : Strategy n L T,
      I.Cvar x ≤ I.B - Γ.card * I.f → (∀ t : Fin T, 1 ≤ t.val → t ∉ Γ → Delta x t = 0) →
      I.Feasible x) ∧
    (∀ x : Strategy n L T, I.Feasible x →
      I.Cvar x ≤ I.B - (changeSet x).card * I.f ∧
      ∀ t : Fin T, 1 ≤ t.val → t ∉ changeSet x → Delta x t = 0) := by sorry

end MenuCostPricing
