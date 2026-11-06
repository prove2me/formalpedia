-- Prove2me | Theorems.Thm_IntConeFPT_lemma_7
-- name    : IntConeFPT.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:23.149708+00:00
-- url     : https://prove2.me/theorems/1a2b7ab6-11e8-4cab-821e-763b5a0f692a
-- title:
--   Lemma 7 (Support Bound) — at most $2^d$ generators per type, same aggregates and counts, no larger cost
-- statement:
--   Let $d\ge1$, let $P^{(1)},\dots,P^{(\tau)}\subseteq\mathbb R^{d+k}$ be bounded convex sets, $S^{(t)}=P^{(t)}\cap(\mathbb Z^d\times\mathbb R^k)$, $X^{(t)}=P^{(t)}_x\cap\mathbb Z^d$, and let each $f^{(t)}$ satisfy the discrete Jensen inequality on $X^{(t)}$. For every finitely supported $\lambda=(\lambda^{(t)}_{(x,u)})$ with values in $\mathbb Z_{\ge0}$ and $\lambda^{(t)}$ supported in $S^{(t)}$, there is a finitely supported $\tilde\lambda$ of the same kind such that for every type $t$:
--
--   1. $\sum\tilde\lambda^{(t)}_{(x,u)}(x,u)=\sum\lambda^{(t)}_{(x,u)}(x,u)$ and $\sum\tilde\lambda^{(t)}_{(x,u)}=\sum\lambda^{(t)}_{(x,u)}$;
--   2. $\sum\tilde\lambda^{(t)}_{(x,u)}f^{(t)}(x)\le\sum\lambda^{(t)}_{(x,u)}f^{(t)}(x)$;
--   3. $|\{(x,u)\in S^{(t)}:\tilde\lambda^{(t)}_{(x,u)}>0\}|\le2^d$.
--
--   In particular the total support satisfies $|\operatorname{supp}\tilde\lambda|\le\tau2^d$.
--
--   This is a mixed-integer, cost-aware form of the Eisenbrand–Shmonin support bound; it limits the number of active residue classes per type to $2^d$.
--
--   **Formalization Note** $d\ge1$ is the paper's standing assumption (p.2). Supports are counted with `Finsupp.support`.
--
--   Differences from the source:
--   - encoding: f^(t) : P_x^(t) → R → f t : (Fin d → ℝ) → ℝ, with the discrete Jensen hypothesis on X^(t) only; reason: only the values on X^(t) enter the hypotheses and conclusions; every function on P_x^(t) extends to ℝ^d
--   - encoding: finitely supported λ = (λ^(t)_(x,u))_{t∈[τ],(x,u)∈S^(t)} → λ t : (Fin d → ℤ) × (Fin k → ℝ) →₀ ℕ with support ⊆ S^(t); reason: Lean convention; same objects
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Lemma 7, p.10

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Problem

open OnlineCRS.Combine

namespace IntConeFPT

/-- **Lemma 7 (Support Bound).**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Lemma 7, p.10: "Let P^(1), …, P^(τ) ⊆ R^{d+k} be bounded
convex sets, let S^(t) := P^(t) ∩ (Z^d × R^k), and let f^(t) : P_x^(t) → R satisfy the discrete
Jensen inequality in Assumption 3 for each t ∈ [τ]. For any finitely supported collection of
coefficients λ … with λ^(t)_(x,u) ∈ Z≥0, there exists a finitely supported collection λ̃ … with
λ̃^(t)_(x,u) ∈ Z≥0 such that for every type t ∈ [τ]: 1. [same aggregate and same count], 2. [cost
not larger], and 3. |{(x, u) ∈ S^(t) : λ̃^(t)_(x,u) > 0}| ≤ 2^d. In particular, the total support
across all types satisfies |supp(λ̃)| ≤ τ2^d."

**Formalization Note.** `d ≥ 1` is the paper's standing assumption (p.2). `P_x^(t)` is the
projection of `P^(t)` to the first `d` coordinates and `X^(t) = P_x^(t) ∩ Z^d`; the discrete Jensen
inequality is required on `X^(t)` only. The cost `f^(t)` is given on all of `R^d`; only its values
on `X^(t)` enter. -/
theorem lemma_7 {d k τ : ℕ} (hd : 1 ≤ d) (P : Fin τ → Set ((Fin d → ℝ) × (Fin k → ℝ)))
    (hconv : ∀ t, Convex ℝ (P t)) (hbdd : ∀ t, Bornology.IsBounded (P t))
    (f : Fin τ → (Fin d → ℝ) → ℝ)
    (hf : ∀ t, DiscreteJensen {x : Fin d → ℤ | (fun i => (x i : ℝ)) ∈ Prod.fst '' P t}
      (fun x => f t (fun i => (x i : ℝ))))
    (μ : (t : Fin τ) → Gen d k →₀ ℕ)
    (hμ : ∀ t, (↑(μ t).support : Set (Gen d k)) ⊆ genSet (P t)) :
    ∃ μ' : (t : Fin τ) → Gen d k →₀ ℕ,
      (∀ t, (↑(μ' t).support : Set (Gen d k)) ⊆ genSet (P t)) ∧
      (∀ t, aggr (μ' t) = aggr (μ t) ∧ count (μ' t) = count (μ t)) ∧
      (∀ t, costOf (f t) (μ' t) ≤ costOf (f t) (μ t)) ∧
      (∀ t, (μ' t).support.card ≤ 2 ^ d) ∧
      ∑ t, (μ' t).support.card ≤ τ * 2 ^ d := by sorry

end IntConeFPT
