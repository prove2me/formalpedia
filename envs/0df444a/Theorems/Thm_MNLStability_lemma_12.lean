-- Prove2me | Theorems.Thm_MNLStability_lemma_12
-- name    : MNLStability.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:39.828186+00:00
-- url     : https://prove2.me/theorems/43a28593-3372-490d-b034-4e4f31f42ea8
-- title:
--   Lemma 12 — scaling down $w_a$ raises the consumption of all other products (up-set form)
-- statement:
--   Let $\tilde w$ be $w$ with the weight of product $a$ (product $1$ in the paper) scaled to $\tilde w_a=(1-\varepsilon)w_a$, $\varepsilon\in[0,1)$. For every inventory vector $U$, every number of customers $m$ and every up-set $A$ of consumption outcomes $(X,X_0)$ that ignores product $a$,
--
--   $$\Pr_{\tilde w}\bigl[(X^U(m),X^U_0(m))\in A\bigr]\ \ge\ \Pr_{w}\bigl[(X^U(m),X^U_0(m))\in A\bigr].$$
--
--   That is, the consumption vector of the products other than $a$, with the no-purchase option, is stochastically larger under $\tilde w$. The paper states the inequality $\mathbb E_{\tilde w}[X^U_C(m)]\ge\mathbb E_w[X^U_C(m)]$ for the events $\{X_j\ge C_j\ \forall j\}$ with $C_1=0$, the principal up-sets; it yields Lemma 10 (item 2 of Theorem 2) and, through Lemma 13, item 1.
--
--   Differences from the source:
--   - generalization: E_w̃[X_C^U(m)] ≥ E_w[X_C^U(m)] for C ≤ U, C₁ = 0 (the principal up-sets {x ≥ C}) → every up-set of consumption vectors that ignores product a; reason: §5.4 applies Strassen's theorem to the relation ≽st, which needs all up-sets, while p.26's "equivalent" holds only for the orthant order; the proof of §5.2 and App. A.7 works verbatim for an up-set indicator, and the printed lemma is the case A = {x ≥ C}
--   - encoding: product 1 ("without loss of generality", p.10) → an arbitrary product a; reason: relabeling; the paper's case is a = product 1
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Lemma 12, p.26; proof §5.2, pp.26–30

import Mathlib
import Definitions.Def_MNLStability_prob
import Definitions.Def_MNLStability_IsUpSetOff
import Definitions.Def_MNLStability_scaleProd

namespace MNLStability

/-- **Lemma 12** (SSRN:3498325, p.26; proof §5.2, pp.26–30), in up-set form. Let `w̃` be `w` with the
weight of product `a` scaled to `(1 − ε)·w_a`, `ε ∈ [0, 1)`. For every inventory vector `U`, every
number of customers `m`, and every up-set `A` of consumption vectors `(X, X₀)` that ignores
product `a`: `Pr_w̃[(X^U(m), X₀^U(m)) ∈ A] ≥ Pr_w[(X^U(m), X₀^U(m)) ∈ A]`.

The printed lemma, `E_w̃[X^U_C(m)] ≥ E_w[X^U_C(m)]` for `C ≤ U` with `C₁ = 0`, is the case
`A = {x : x ≥ C}`. -/
theorem lemma_12 {n : ℕ} (wts : Weights n) (hw : wts.Pos) (a : Fin n) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) (U : Fin n → ℕ) (m : ℕ) (A : Set ((Fin n → ℕ) × ℕ)) (hA : IsUpSetOff a A) :
    prob wts U m A ≤ prob (scaleProd wts a ε) U m A := by sorry

end MNLStability
