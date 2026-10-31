-- Prove2me | Theorems.Thm_MultiUnitProphet_eq_4_1
-- name    : MultiUnitProphet.eq_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:21.447992+00:00
-- url     : https://prove2.me/theorems/38a663c6-1e0f-4138-8dec-d108d7af3be0
-- title:
--   Eq. (4.1) — $\mathrm{Opt}(k,\mathcal F)\le kp+\sum_t\mathbb P[t\in Z_p]\,\mathbb E[v_t-p\mid t\in Z_p]$
-- statement:
--   Let $k\ge1$, let $\mathcal F$ be an instance with $n$ buyers, $p\in\mathbb R$, and let $Z_p$ be the random set of buyers whose value exceeds $p$. If $n\ge k$ or $p\ge0$, then
--
--   $$\mathrm{Opt}(k,\mathcal F)\ \le\ kp+\sum_{t\in[n]}\mathbb P[t\in Z_p]\,\mathbb E[v_t-p\mid t\in Z_p]\ =\ kp+\sum_{t\in[n]}\mathbb E[\max(0,v_t-p)].$$
--
--   The first summand is the most revenue the seller can collect at price $p$ ($R_k(p)=kp$), the second the most utility the buyers can collect ($U(p)$). Lemma 1 compares the welfare of the price $p$ with this bound.
--
--   **Formalization Note** In $[0,\infty]$ the inequality is written $\mathrm{Opt}+\max(0,-kp)\le\max(0,kp)+U(p)$, which is the real inequality for every sign of $p$ and also covers $\mathrm{Opt}=U(p)=\infty$.
--
--   Differences from the source:
--   - encoding: a supply k (a positive integer) → k : ℕ with 1 ≤ k; reason: the supply is a positive number of units; at k = 0 the quantities are degenerate
--   - encoding: n distributions on the nonnegative reals, buyer t drawn independently from F_t, F_t the t-th arriving distribution → F : Fin n → Measure ℝ with IsInstance F (probability measures with F t (−∞,0) = 0), values drawn from Measure.pi F, index order = arrival order; reason: Lean convention for independent values; the arrival order is arbitrary because every F is quantified
--   - encoding: P[t ∈ Z_p] · E[v_t − p | t ∈ Z_p] → E[max(0, v_t − p)] (surplus F p, a lower integral of ENNReal.ofReal (v t − p)); reason: the two are equal and the Lean form needs no division by a possibly zero probability
--   - encoding: a ratio Welfare/Opt or a real inequality → a product inequality in ℝ≥0∞ between lower Lebesgue integrals; reason: equivalent when 0 < Opt < ∞, covers Opt = ∞, and needs no finite-mean hypothesis
--   - generalization: the standing atomless assumption of §2, p.7 → stated for every instance, atoms allowed; reason: the statement holds verbatim with atoms when buyers buy at value ≥ p (X_p counts v_t ≥ p); atomless instances are a special case
--   - generalization: the standing assumption n > k (§2, p.7) → k ≤ n ∨ 0 ≤ p; reason: n > k implies the Lean hypothesis; for p < 0 and n < k the inequality is false (n = 1, k = 2, v = 0, p = −1)
--   - reading: the chain of inequalities (4.1) → its outer inequality Opt ≤ kp + Σ_t P[t ∈ Z_p] E[v_t − p | t ∈ Z_p]; reason: the intermediate expressions are pointwise proof steps and the last step is an equality; the outer inequality is the content used in the proof of Lemma 1
--   - generalization: the WLOG assumption P[v_t > 0] > 0 (§2, p.7) → instances may contain buyers with v_t = 0 almost surely; reason: the Lean statement is true on these instances too, and instances satisfying the WLOG are a special case
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, §4, eq. (4.1), p.9

import Mathlib
import Definitions.Def_MultiUnitProphet_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **Eq. (4.1): the revenue-plus-utility upper bound on `Opt`.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, §4, eq. (4.1), p.9:
`Opt(k, F) ≤ kp + Σ_{t ∈ [n]} P[t ∈ Z_p] E[v_t − p | t ∈ Z_p]`, where `Z_p` is the random set of
buyers whose value exceeds the price `p`.

**Formalization Note.** `Σ_t P[t ∈ Z_p] E[v_t − p | t ∈ Z_p] = Σ_t E[max(0, v_t − p)]` is `surplus F p`
(p.9: "U(p) = Σ_t E[max(0, v_t − p)]"). In `ℝ≥0∞` the real inequality `Opt ≤ kp + U(p)` is written
`Opt + max(0, −kp) ≤ max(0, kp) + U(p)`, which is the same inequality for every real `p`. It is
stated under `k ≤ n ∨ 0 ≤ p` (the paper's standing assumption is `n > k`; for `p < 0` and `n < k` the
inequality fails). -/
theorem eq_4_1 (k n : ℕ) (hk : 1 ≤ k) (F : Fin n → Measure ℝ) (hF : IsInstance F) (p : ℝ)
    (hp : k ≤ n ∨ 0 ≤ p) :
    opt k F + ENNReal.ofReal (-((k : ℝ) * p)) ≤ ENNReal.ofReal ((k : ℝ) * p) + surplus F p := by sorry

end MultiUnitProphet
