-- Prove2me | Theorems.Thm_MNLStability_lemma_3
-- name    : MNLStability.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:14.442853+00:00
-- url     : https://prove2.me/theorems/d2eece26-484b-41cb-ba4d-46e02ffad310
-- title:
--   Lemma 3 — rounding the weights down loses at most a factor $1-\varepsilon$
-- statement:
--   Let $w^\downarrow$ be product weights with $(1-\varepsilon)\,w_i\le w^\downarrow_i\le w_i$ and $w^\downarrow_i>0$ for every product, and the same no-purchase weight $w_0$ (the rounding of §3.1 has this property). Then for every inventory vector $U$, with non-negative prices,
--
--   $$\mathbb E\bigl[R_{w^\downarrow}(U)\bigr]\ \ge\ (1-\varepsilon)\cdot\mathbb E\bigl[R_w(U)\bigr].$$
--
--   The paper states it for an optimal vector $U^*$; it is the first link of the chain on p.18.
--
--   Differences from the source:
--   - generalization: the standing assumption of §2.3, p.13 ("in the remainder of this paper, we operate under the opposite scenario of w_max > εw₀/n") → no regime hypothesis; reason: the proof uses no lower bound on purchase probabilities; every instance of the regime is covered
--   - generalization: the optimal vector U* and the rounded weights w↓ of §3.1 → every inventory vector U and every weights w↓ with (1 − ε)w_i ≤ w↓_i ≤ w_i, w↓_i > 0; reason: the proof (p.15) uses only these bounds and never the optimality of U*; the paper's case is an instance
--   - encoding: the number of customers M, finitely supported (p.3) → a law pM : ℕ →₀ ℝ (IsLaw) mixed over its support; reason: Lean convention; same instances
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Lemma 3, p.15

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX

namespace MNLStability

/-- **Lemma 3** (SSRN:3498325, p.15). Let `w↓` be product weights with `(1 − ε)·w_i ≤ w↓_i ≤ w_i`
for every product, and the same no-purchase weight `w₀` (the rounding of §3.1, p.14). Then
`E[R_{w↓}(U)] ≥ (1 − ε)·E[R_w(U)]`; the paper states it for an optimal vector `U*`. -/
theorem lemma_3 {n : ℕ} (wts : Weights n) (hw : wts.Pos) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (ε : ℝ) (hε : 0 < ε) (wd : Fin n → ℝ) (hwd0 : ∀ i, 0 < wd i)
    (hwd : ∀ i, (1 - ε) * wts.w i ≤ wd i ∧ wd i ≤ wts.w i) (U : Fin n → ℕ) :
    (1 - ε) * expR wts r pM U ≤ expR ⟨wts.w0, wd⟩ r pM U := by sorry

end MNLStability
