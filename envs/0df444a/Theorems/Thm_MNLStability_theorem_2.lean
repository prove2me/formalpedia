-- Prove2me | Theorems.Thm_MNLStability_theorem_2
-- name    : MNLStability.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:55.325352+00:00
-- url     : https://prove2.me/theorems/17bf0fc6-5cd2-46d4-b19e-c245089a58f7
-- title:
--   Theorem 2 — stability of MNL demand under scaling one weight
-- statement:
--   Scale the preference weight of a product $a$ (product $1$ in the paper) to $\tilde w_a=(1-\varepsilon)w_a$, where $\varepsilon\in[0,1)$, and keep every other weight, including $w_0$. For any inventory vector $U$, with the number of customers $M$ random with a finitely supported law:
--
--   1. $\mathbb E_{\tilde w}[X_a^U]\ \ge\ (1-\varepsilon)\,\mathbb E_w[X_a^U]$;
--   2. $\mathbb E_{\tilde w}[X_i^U]\ \ge\ \mathbb E_w[X_i^U]$ for every product $i\ne a$.
--
--   Scaling one weight down costs that product at most the same factor of its expected demand, and can only help every other product. This is the engine of the rounding steps (Lemmas 3 and 5). Lemmas 10 and 11 (p.25) are the two items for a deterministic number of customers.
--
--   Differences from the source:
--   - encoding: product 1 ("without loss of generality", p.10) → an arbitrary product a; reason: relabeling; the paper's case is a = product 1
--   - encoding: the number of customers M, finitely supported (p.3) → a law pM : ℕ →₀ ℝ (IsLaw) mixed over its support; reason: Lean convention; same instances
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Theorem 2, p.11; proof §5, pp.25–31 (Lemmas 10, 11, p.25)

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_scaleProd

namespace MNLStability

/-- **Theorem 2** (SSRN:3498325, p.11; proof §5, with Lemmas 10 and 11, p.25). Scale the preference
weight of product `a` (product `1` in the paper) to `w̃_a = (1 − ε)·w_a`, `ε ∈ [0, 1)`, keeping every
other weight. For any inventory vector `U`:
1. `E_w̃[X_a^U] ≥ (1 − ε)·E_w[X_a^U]`;
2. `E_w̃[X_i^U] ≥ E_w[X_i^U]` for every `i ≠ a`. -/
theorem theorem_2 {n : ℕ} (wts : Weights n) (hw : wts.Pos) (pM : ℕ →₀ ℝ) (hM : IsLaw pM)
    (a : Fin n) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (U : Fin n → ℕ) :
    (1 - ε) * expX wts pM U a ≤ expX (scaleProd wts a ε) pM U a ∧
      ∀ i, i ≠ a → expX wts pM U i ≤ expX (scaleProd wts a ε) pM U i := by sorry

end MNLStability
