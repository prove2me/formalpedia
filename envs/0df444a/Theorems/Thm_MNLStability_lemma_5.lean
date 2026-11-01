-- Prove2me | Theorems.Thm_MNLStability_lemma_5
-- name    : MNLStability.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:22.544696+00:00
-- url     : https://prove2.me/theorems/4677e14a-546a-421b-b047-469d93d28761
-- title:
--   Lemma 5 — restoring the original weights loses at most a factor $1-\varepsilon$
-- statement:
--   Let $w^\downarrow$ be product weights with $w_i/(1+\varepsilon)\le w^\downarrow_i\le w_i$ for every product, and the same no-purchase weight $w_0$ (the rounding of §3.1 has this property). Then for every inventory vector $U$, with non-negative prices,
--
--   $$\mathbb E\bigl[R_w(U)\bigr]\ \ge\ (1-\varepsilon)\cdot\mathbb E\bigl[R_{w^\downarrow}(U)\bigr].$$
--
--   The paper states it for the returned vector $\hat U$; it is the last link of the chain on p.18.
--
--   Differences from the source:
--   - generalization: the standing assumption of §2.3, p.13 ("in the remainder of this paper, we operate under the opposite scenario of w_max > εw₀/n") → no regime hypothesis; reason: the proof uses no lower bound on purchase probabilities; every instance of the regime is covered
--   - generalization: the returned vector Û and the rounded weights w↓ of §3.1 → every inventory vector U and every weights w↓ with w_i/(1 + ε) ≤ w↓_i ≤ w_i; reason: the proof uses only these bounds; the paper's case is an instance
--   - encoding: the number of customers M, finitely supported (p.3) → a law pM : ℕ →₀ ℝ (IsLaw) mixed over its support; reason: Lean convention; same instances
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Lemma 5, p.17

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX

namespace MNLStability

/-- **Lemma 5** (SSRN:3498325, p.17). Let `w↓` be product weights with `w_i/(1 + ε) ≤ w↓_i ≤ w_i` for
every product, and the same no-purchase weight `w₀` (the rounding of §3.1, p.14). Then
`E[R_w(U)] ≥ (1 − ε)·E[R_{w↓}(U)]`; the paper states it for the returned vector `Û`. -/
theorem lemma_5 {n : ℕ} (wts : Weights n) (hw : wts.Pos) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (ε : ℝ) (hε : 0 < ε) (wd : Fin n → ℝ)
    (hwd : ∀ i, wts.w i / (1 + ε) ≤ wd i ∧ wd i ≤ wts.w i) (U : Fin n → ℕ) :
    (1 - ε) * expR ⟨wts.w0, wd⟩ r pM U ≤ expR wts r pM U := by sorry

end MNLStability
