-- Prove2me | Theorems.Thm_MultiUnitProphet_eq_4_3
-- name    : MultiUnitProphet.eq_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:13:26.766239+00:00
-- url     : https://prove2.me/theorems/c6eb78cf-762b-4755-b292-d2c524f1ad6a
-- title:
--   Eq. (4.3) — $\mathrm{Utility}(p,k,\mathcal F)\ge\delta_k(X_p)\sum_t\mathbb P[t\in Z_p]\,\mathbb E[v_t-p\mid t\in Z_p]$
-- statement:
--   Let $k\ge1$, let $\mathcal F$ be an instance with $n$ buyers in any arrival order, and $p\in\mathbb R$. A buyer $t$ receives utility $v_t-p$ iff $v_t\ge p$ and a unit is still available when she arrives; whatever the order, the latter happens with probability at least the probability $\delta_k(X_p)=\mathbb P[X_p\le k-1]$ that the units do not sell out. Hence
--
--   $$\mathrm{Utility}(p,k,\mathcal F)\ \ge\ \sum_{t\in[n]}\delta_k(X_p)\cdot\mathbb P[t\in Z_p]\,\mathbb E[v_t-p\mid t\in Z_p].$$
--
--   Together with (4.1) and the revenue identity (4.2) this gives Lemma 1.
--
--   **Formalization Note** $\mathbb P[t\in Z_p]\,\mathbb E[v_t-p\mid t\in Z_p]=\mathbb E[\max(0,v_t-p)]$; both sides are in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: a supply k (a positive integer) → k : ℕ with 1 ≤ k; reason: the supply is a positive number of units; at k = 0 the quantities are degenerate
--   - encoding: n distributions on the nonnegative reals, buyer t drawn independently from F_t, F_t the t-th arriving distribution → F : Fin n → Measure ℝ with IsInstance F (probability measures with F t (−∞,0) = 0), values drawn from Measure.pi F, index order = arrival order; reason: Lean convention for independent values; the arrival order is arbitrary because every F is quantified
--   - encoding: P[t ∈ Z_p] · E[v_t − p | t ∈ Z_p] → E[max(0, v_t − p)] (surplus F p, a lower integral of ENNReal.ofReal (v t − p)); reason: the two are equal and the Lean form needs no division by a possibly zero probability
--   - encoding: a ratio Welfare/Opt or a real inequality → a product inequality in ℝ≥0∞ between lower Lebesgue integrals; reason: equivalent when 0 < Opt < ∞, covers Opt = ∞, and needs no finite-mean hypothesis
--   - reading: the buyer purchases iff her value is above the price (§2, p.6) → buys iff v_t ≥ p and fewer than k earlier buyers have v_s ≥ p; reason: matches X_p := |{t : v_t ≥ p}| (p.7), which the paper's analysis uses; for atomless laws the tie v_t = p has probability 0
--   - generalization: the standing atomless assumption of §2, p.7 → stated for every instance, atoms allowed; reason: the statement holds verbatim with atoms when buyers buy at value ≥ p (X_p counts v_t ≥ p); atomless instances are a special case
--   - generalization: the WLOG assumptions n > k and P[v_t > 0] > 0 (§2, p.7) → every n and every instance, buyers with v_t = 0 almost surely included; reason: the Lean statement is true on these instances too, and instances satisfying the WLOG are a special case
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, §4, eq. (4.3), p.9

import Mathlib
import Definitions.Def_MultiUnitProphet_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiUnitProphet

/-- **Eq. (4.3): the utility lower bound.**
Chawla, Devanur & Lykouris, *Static pricing for multi-unit prophet inequalities*,
arXiv:2007.07990v4, §4, eq. (4.3), p.9: "Regardless of the order in which buyers arrive, the latter event
happens with probability at least as large as the probability that the item is not sold out at the
end of the process. … Utility(p, k, F) ≥ Σ_{t ∈ [n]} δk(Xp) · P[t ∈ Zp] E[vt − p | t ∈ Zp]."

**Formalization Note.** `Σ_t P[t ∈ Z_p] E[v_t − p | t ∈ Z_p] = surplus F p = Σ_t E[max(0, v_t − p)]`;
products and sums in `ℝ≥0∞`. The order of arrival is the index order of `Fin n`, arbitrary since
`F` is. -/
theorem eq_4_3 (k n : ℕ) (hk : 1 ≤ k) (F : Fin n → Measure ℝ) (hF : IsInstance F) (p : ℝ) :
    ENNReal.ofReal (delta k F p) * surplus F p ≤ utility k F p := by sorry

end MultiUnitProphet
