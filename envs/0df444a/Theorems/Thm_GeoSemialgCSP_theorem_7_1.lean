-- Prove2me | Theorems.Thm_GeoSemialgCSP_theorem_7_1
-- name    : GeoSemialgCSP.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:18.719573+00:00
-- url     : https://prove2.me/theorems/640ab276-f773-43dc-b361-7e681db90228
-- title:
--   Theorem 7.1 — semialgebraic partition theorem
-- statement:
--   Let $P$ be a semialgebraic predicate on $(\mathbb R^d)^k$, $k\ge2$. There are a constant $d_{\mathrm{fVC}}(P)$, a constant $K_P$ and a semialgebraic formula $\theta(x;y)$ with $x\in\mathbb R^d$, $y\in\mathbb R^p$, all depending only on $P$, such that, writing $C(y)=\{x:\theta(x;y)\}$: for every finitely supported probability measure $\mu_X$ on $\mathbb R^d$ and every $0<\varepsilon<1$ there is a partition $\mathbb R^d=C_0\sqcup\dots\sqcup C_{q-1}$ into
--   $$q\ \le\ K_P\,\varepsilon^{-K_P}$$
--   nonempty cells, each of the form $C_a=C(y_a)$. With $\mu(a)=\mu_X(C_a)$ and
--   $$\Delta=\{(a_1,\dots,a_k):\ P\text{ is not constant on }C_{a_1}\times\dots\times C_{a_k}\},\tag{14}$$
--
--   1. (a) $\mu_X^{\otimes k}\bigl(\bigcup_{a\in\Delta}C_{a_1}\times\dots\times C_{a_k}\bigr)=\mu^{\otimes k}(\Delta)\le\varepsilon$;
--   2. (b) $\mathrm{fVC}(\Delta)\le d_{\mathrm{fVC}}(P)$.
--
--   The formula $\theta$ and the bound $d_{\mathrm{fVC}}(P)$ are independent of $\mu_X$ and $\varepsilon$. The theorem controls exceptional cell tuples for independent samples; Sections 8–9 extend this to the correlated queries of the test.
--
--   Differences from the source:
--   - encoding: a predicate P : (ℝ^d)^k → {0,1}, semialgebraic in the k·d coordinates → its accepting set S ⊆ (EuclideanSpace ℝ (Fin d))^k, semialgebraic through finProdFinEquiv; reason: the same predicate; P(x) = 1 iff x ∈ S
--   - encoding: a semialgebraic formula θ(x; y), x ∈ ℝ^d, y ∈ ℝ^p → its solution set Θ ⊆ ℝ^{d+p} (point coordinates first), semialgebraic; reason: a formula and its solution set define the same family C(y)
--   - encoding: q ≤ N_P(ε) with N_P a polynomial in 1/ε and N_P(ε) ≤ K_P ε^{−K_P} → q ≤ K_P ε^{−K_P} (Real.rpow); reason: equivalent: from the bound, N_P(ε) = ⌈K_P⌉ ε^{−⌈K_P⌉} is such a polynomial (K_P > 0 since q ≥ 1)
--   - encoding: a finitely supported probability measure μ_X on ℝ^d → atoms x : Fin n → E d with masses w in the simplex; reason: same measures
--   - encoding: P is not constant on C_{a₁} × ⋯ × C_{a_k} → some tuple of the product is in S and some is not; reason: same condition
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 7.1, Eq. (14), p.20 (PDF p.21), based on Chernikov–Starchenko 2021, Theorem 4.16

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_IsSemialgebraicPred
import Definitions.Def_NonconvexSplitting_ADMMKL_Semialgebraic
import Definitions.Def_GeoSemialgCSP_PartitionFormula

namespace GeoSemialgCSP

/-- **Theorem 7.1 (semialgebraic partition theorem).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 7.1, Eq. (14), printed p.20
(PDF p.21), based on Chernikov–Starchenko (2021, Theorem 4.16): for a semialgebraic predicate `P`
on `(ℝ^d)^k`, `k ≥ 2`, there are `d_fVC(P)`, `N_P(ε) ≤ K_P ε^{−K_P}` and a semialgebraic formula
`θ(x; y)` (`x ∈ ℝ^d`, `y ∈ ℝ^p`) such that for every finitely supported probability measure `μ_X`
on `ℝ^d` and every `0 < ε < 1` there is a partition `ℝ^d = C₀ ⊔ ⋯ ⊔ C_{q−1}` into `q ≤ N_P(ε)`
nonempty cells `C_a = C(y_a)`, and, with `μ(a) = μ_X(C_a)` and `Δ` the tuples on whose product `P`
is not constant, (a) `μ_X^{⊗k}(⋃_{a ∈ Δ} C_{a₁} × ⋯ × C_{a_k}) = μ^{⊗k}(Δ) ≤ ε` and
(b) `fVC(Δ) ≤ d_fVC(P)`. `θ` and `d_fVC(P)` are independent of `μ_X` and `ε`.

**Formalization Note.** `θ` is its solution set `Θ ⊆ ℝ^{d+p}` (point coordinates first); the
"following property" is `PartitionFormula S dfVC KP Θ`. The quantifier order (`∃ dfVC KP p Θ`
before the `∀ μ_X ε` inside `PartitionFormula`) makes `θ`, `d_fVC`, `K_P` independent of `μ_X`
and `ε`. -/
theorem theorem_7_1 {k d : ℕ} (hk : 2 ≤ k) (S : Set (Fin k → E d)) (hsa : IsSemialgebraicPred S) :
    ∃ (dfVC : ℕ) (KP : ℝ) (p : ℕ) (Θ : Set (Fin (d + p) → ℝ)),
      NonconvexSplitting.ADMMKL.IsSemialgebraicSet Θ ∧ PartitionFormula S dfVC KP Θ := by sorry

end GeoSemialgCSP
