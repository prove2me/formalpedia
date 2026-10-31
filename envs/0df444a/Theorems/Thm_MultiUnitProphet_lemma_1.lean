-- Prove2me | Theorems.Thm_MultiUnitProphet_lemma_1
-- name    : MultiUnitProphet.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:17.94299+00:00
-- url     : https://prove2.me/theorems/581c518e-a494-4b41-999b-e90d66c82b7e
-- title:
--   Lemma 1 — $\mathrm{Welfare}(p,k,\mathcal F)\ge\min(\delta_k(X_p),\mu_k(X_p))\,\mathrm{Opt}(k,\mathcal F)$ for every price
-- statement:
--   For any supply $k\ge1$, any instance $\mathcal F$ with $n$ buyers in any arrival order and any price $p\in\mathbb R$,
--
--   $$\frac{\mathrm{Welfare}(p,k,\mathcal F)}{\mathrm{Opt}(k,\mathcal F)}\ \ge\ \min\big(\delta_k(X_p),\mu_k(X_p)\big).$$
--
--   This is the paper's revenue–utility decomposition: the revenue earns a $\mu_k(X_p)$ fraction of $kp$ and the utility a $\delta_k(X_p)$ fraction of $U(p)$, and $kp+U(p)\ge\mathrm{Opt}$. It is the first half of Theorem 1.
--
--   **Formalization Note** Written as $\min(\delta_k(X_p),\mu_k(X_p))\cdot\mathrm{Opt}\le\mathrm{Welfare}$ in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: a supply k (a positive integer) → k : ℕ with 1 ≤ k; reason: the supply is a positive number of units; at k = 0 the quantities are degenerate
--   - encoding: n distributions on the nonnegative reals, buyer t drawn independently from F_t, F_t the t-th arriving distribution → F : Fin n → Measure ℝ with IsInstance F (probability measures with F t (−∞,0) = 0), values drawn from Measure.pi F, index order = arrival order; reason: Lean convention for independent values; the arrival order is arbitrary because every F is quantified
--   - encoding: a ratio Welfare/Opt or a real inequality → a product inequality in ℝ≥0∞ between lower Lebesgue integrals; reason: equivalent when 0 < Opt < ∞, covers Opt = ∞, and needs no finite-mean hypothesis
--   - reading: the buyer purchases iff her value is above the price (§2, p.6) → buys iff v_t ≥ p and fewer than k earlier buyers have v_s ≥ p; reason: matches X_p := |{t : v_t ≥ p}| (p.7), which the paper's analysis uses; for atomless laws the tie v_t = p has probability 0
--   - generalization: the standing atomless assumption of §2, p.7 → stated for every instance, atoms allowed; reason: the statement holds verbatim with atoms when buyers buy at value ≥ p (X_p counts v_t ≥ p); atomless instances are a special case
--   - generalization: the WLOG assumptions n > k and P[v_t > 0] > 0 (§2, p.7) → every n and every instance, buyers with v_t = 0 almost surely included; reason: the Lean statement is true on these instances too, and instances satisfying the WLOG are a special case
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, Lemma 1, p.7 (proof §4, p.9)

import Mathlib
import Definitions.Def_MultiUnitProphet_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **Lemma 1: the welfare of any static price is at least `min(δ_k(X_p), µ_k(X_p))` times `Opt`.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, Lemma 1, p.7 (restated and proved in §4, p.9): "For any supply k, set of distributions F,
and any price p ∈ R: Welfare(p, k, F)/Opt(k, F) ≥ min(δk(Xp), µk(Xp))."

**Formalization Note.** The ratio is written as the product
`min(δ_k(X_p), µ_k(X_p)) · Opt(k, F) ≤ Welfare(p, k, F)` in `ℝ≥0∞`, which is the ratio inequality
when `0 < Opt < ∞` and also covers `Opt = ∞`. Atoms are allowed; a buyer buys iff `v_t ≥ p` and a
unit is left. -/
theorem lemma_1 (k n : ℕ) (hk : 1 ≤ k) (F : Fin n → Measure ℝ) (hF : IsInstance F) (p : ℝ) :
    ENNReal.ofReal (min (delta k F p) (mu k F p)) * opt k F ≤ welfare k F p := by sorry

end MultiUnitProphet
