-- Prove2me | Theorems.Thm_MNLStability_claim_3
-- name    : MNLStability.claim_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:44.737253+00:00
-- url     : https://prove2.me/theorems/5f71ec62-0743-4119-8a4c-388c3397e8b8
-- title:
--   Claim 3 — $t$ extra units of product $1$ absorb at most $t$ customers (up-set form)
-- statement:
--   Fix MNL weights, a product $a$ (product $1$ in the paper), an inventory vector $V$, integers $0\le t\le m$, and an up-set $A$ of consumption outcomes $(X,X_0)$ that ignores product $a$ (including the no-purchase count). Then
--
--   $$\Pr\bigl[(X^V(m),X^V_0(m))\in A\bigr]\ \ge\ \Pr\bigl[(X^{V-te_a}(m-t),X^{V-te_a}_0(m-t))\in A\bigr],$$
--
--   where $V-te_a$ is truncated at $0$ (the convention $(X-Y)_i=[X_i-Y_i]^+$ of p.27).
--
--   The paper states it for the events $\{X_j\ge C_j\ \forall j\}$ with $C\le V$ and $C_1=0$, which are the principal up-sets; it is the time-shifting step in the proof of Lemma 12.
--
--   Differences from the source:
--   - generalization: the events X_C (at least C_j units of every j ∈ [n] ∪ {0}), C ≤ V, C₁ = 0 → every up-set of consumption vectors that ignores product a; reason: the proof of App. A.7 goes through with an up-set indicator in place of X_C; the printed claim is the case A = {x ≥ C}, and Lemma 13 needs all up-sets (the orthant events do not give the stochastic order Strassen's theorem needs, p.26)
--   - encoding: product 1 ("without loss of generality", p.10) → an arbitrary product a; reason: relabeling; the paper's case is a = product 1
--   - encoding: customers m, deterministic → a fixed m : ℕ, probabilities of the m-customer process; reason: the claim is stated for a deterministic number of customers
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Claim 3, p.30; proof App. A.7, p.48

import Mathlib
import Definitions.Def_MNLStability_prob
import Definitions.Def_MNLStability_IsUpSetOff

namespace MNLStability

/-- **Claim 3** (SSRN:3498325, p.30; proof App. A.7, p.48), in up-set form. For any weights, any
product `a` (product `1` in the paper), any inventory vector `V`, any integers `0 ≤ t ≤ m`, and any
up-set `A` of consumption vectors `(X, X₀)` that ignores product `a`:
`Pr[(X^V(m), X₀^V(m)) ∈ A] ≥ Pr[(X^{V − t e_a}(m − t), X₀^{V − t e_a}(m − t)) ∈ A]`,
where `V − t e_a` is truncated at `0` (p.27).

The printed claim, `E_w̃[X^V_C(m)] ≥ E_w̃[X^{V−te₁}_C(m − t)]` for `C ≤ V` with `C₁ = 0`, is the case
`A = {x : x ≥ C}`. -/
theorem claim_3 {n : ℕ} (wts : Weights n) (hw : wts.Pos) (a : Fin n) (V : Fin n → ℕ) (t m : ℕ)
    (htm : t ≤ m) (A : Set ((Fin n → ℕ) × ℕ)) (hA : IsUpSetOff a A) :
    prob wts (V - t • Pi.single a 1) (m - t) A ≤ prob wts V m A := by sorry

end MNLStability
