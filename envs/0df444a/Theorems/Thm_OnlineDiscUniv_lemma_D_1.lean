-- Prove2me | Theorems.Thm_OnlineDiscUniv_lemma_D_1
-- name    : OnlineDiscUniv.lemma_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:08.621194+00:00
-- url     : https://prove2.me/theorems/5a1bf674-8e61-40a1-a296-91bbff0bd847
-- title:
--   Lemma D.1 — empirical moment bounds from Rosenthal's inequality
-- statement:
--   Let $A_{j,i}$, $1\le j\le J_N$, $1\le i\le M$, be such that for each fixed $j$ the variables $(A_{j,i})_{i\le M}$ are independent and identically distributed, and suppose
--   $$
--   J_N\le CN,\qquad M\asymp N,\qquad\sup_{N,j}\mathbb E|A_{j,1}|^p\le C_p\qquad(D.2)
--   $$
--   for some $p\ge2s$. Then, for each fixed $\varepsilon>0$,
--   $$
--   \mathbb P\Big(\max_{j\le J_N}\Big|\frac1M\sum_{i=1}^M|A_{j,i}|^s-\mathbb E|A_{j,1}|^s\Big|>\varepsilon\Big)\le C_{p,s,\varepsilon}J_NM^{-p/(2s)}\le C'_{p,s,\varepsilon}N^{1-p/(2s)}.\qquad(D.3)
--   $$
--   The same estimate holds with $s$ replaced by any $1\le r\le s$.
--
--   The lemma gives polynomial probability bounds for the empirical moments of the drifts used by the algorithm.
--
--   Differences from the source:
--   - generalization: J_N ≤ CN, M ≍ N along a sequence; s the exponent fixed in (4.2) → the first inequality for one array of any size J × M on any probability space; the second for every N, J, M with J ≤ CN and M ≥ c₁N; every real s with 1 ≤ s and 2s ≤ p; reason: specializes to the source's sequence and exponent; only the lower half of M ≍ N is used
--   - encoding: the same estimate with s replaced by any 1 ≤ r ≤ s → covered by the statement at s = r (2r ≤ 2s ≤ p); reason: the quantification over s includes every such r
--   - encoding: centering E|A_{j,1}|^s; random variables A_{j,i} → M^{-1}∑_i E|A_{j,i}|^s; each A_{j,i} measurable, E|A|^p a lower integral; reason: equal for an identically distributed row; random variables are measurable
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Lemma D.1, (D.2)–(D.3), p.35 (PDF p.36)

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace OnlineDiscUniv

/-- **Lemma D.1** (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, printed p.35, PDF p.36).
Let `A_{j,i}`, `1 ≤ j ≤ J_N`, `1 ≤ i ≤ M`, be such that for each fixed `j` the variables
`(A_{j,i})_{i≤M}` are i.i.d., and suppose `J_N ≤ CN`, `M ≍ N`, `sup_{N,j} E|A_{j,1}|^p ≤ C_p` (D.2)
for some `p ≥ 2s`. Then for each fixed `ε > 0`,
`P(max_{j≤J_N} |M^{−1}∑_i |A_{j,i}|^s − E|A_{j,1}|^s| > ε) ≤ C_{p,s,ε} J_N M^{−p/(2s)} ≤ C'_{p,s,ε} N^{1−p/(2s)}`
(D.3). The same estimate holds with `s` replaced by any `1 ≤ r ≤ s`.

**Formalization Note** The statement is for every real `s` with `1 ≤ s` and `2s ≤ p`; the clause
"with `s` replaced by any `1 ≤ r ≤ s`" is the same statement at `r` (as `2r ≤ 2s ≤ p`). The first
inequality is stated for one array of any size `J × M` on any probability space (rows indexed
`j : Fin J`, columns `i : Fin M`), with `C_{p,s,ε}` depending on `p, s, ε, C_p` only. The centering
`E|A_{j,1}|^s` is written as `M^{−1}∑_i E|A_{j,i}|^s` (equal, the row being identically
distributed). The second inequality is stated for `J ≤ CN` and `M ≥ c_1 N`, the half of `M ≍ N` it
uses. Moments `E|A|^p` are lower integrals; `E|A_{j,i}|^s` is a Bochner integral of an integrable
function (`s ≤ p`). -/
theorem lemma_D_1 (p s ε Cp : ℝ) (hs : 1 ≤ s) (hps : 2 * s ≤ p) (hε : 0 < ε) :
    ∃ C₁ : ℝ,
      (∀ (J M : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (A : Fin J → Fin M → Ω → ℝ), (∀ j i, Measurable (A j i)) →
        (∀ j, iIndepFun (fun i => A j i) P) → (∀ j i i', IdentDistrib (A j i) (A j i') P P) →
        (∀ j i, ∫⁻ ω, ‖A j i ω‖ₑ ^ p ∂P ≤ ENNReal.ofReal Cp) →
        P {ω | ∃ j, ε < |(1 / (M : ℝ)) * ∑ i, (|A j i ω| ^ s - ∫ ω', |A j i ω'| ^ s ∂P)|} ≤
          ENNReal.ofReal (C₁ * J * (M : ℝ) ^ (-p / (2 * s)))) ∧
      ∀ C c₁ : ℝ, 0 < c₁ → ∃ C₂ : ℝ, ∀ N J M : ℕ, (J : ℝ) ≤ C * N → c₁ * N ≤ M →
        C₁ * J * (M : ℝ) ^ (-p / (2 * s)) ≤ C₂ * (N : ℝ) ^ (1 - p / (2 * s)) := by sorry

end OnlineDiscUniv
