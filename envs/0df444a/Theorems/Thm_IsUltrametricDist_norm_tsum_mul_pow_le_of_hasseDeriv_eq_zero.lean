-- Prove2me | Theorems.Thm_IsUltrametricDist_norm_tsum_mul_pow_le_of_hasseDeriv_eq_zero
-- name    : IsUltrametricDist.norm_tsum_mul_pow_le_of_hasseDeriv_eq_zero
-- status  : Proved
-- author  : @ebayuser
-- created : 2026-10-04T09:28:37.6825+00:00
-- url     : https://prove2.me/theorems/9b4d766a-8983-4b0e-be55-3d14ef404a86
-- title:
--   A $p$-adic Schwarz lemma for restricted power series with zeros of high order
-- statement:
--   Let $K$ be a complete field with an ultrametric norm. Let $f(X) = \sum_{k \ge 0} c_k X^k$ be a power series with $c_k \to 0$ and $\|c_k\| \le M$ for all $k$ (a restricted power series, which converges on the closed unit disc). Let $0 \le r \le 1$, let $Z \subseteq K$ be a finite set of points with $\|z\| \le r$, and let $T \ge 0$. Assume that $f$ vanishes to order at least $T$ at each point of $Z$: for each $z_0 \in Z$ and each $t < T$,
--   $$\sum_{k \ge t} \binom{k}{t} c_k z_0^{\,k-t} = 0 .$$
--   Then for each $z \in K$ with $\|z\| \le r$,
--   $$\|f(z)\| \;\le\; r^{\,T \cdot |Z|} \, M .$$
--
--   **Proof idea.** A restricted power series that vanishes at a point $z_0$ of the closed unit disc is $(X - z_0)$ times a restricted power series with the same bound $M$ for its coefficients (re-expand at $z_0$; the Gauss norm is multiplicative and $X - z_0$ has Gauss norm $1$). Induction gives $f = \prod_{z_0 \in Z} (X - z_0)^T \cdot g$ with $\|g(z)\| \le M$ on the unit disc. For $\|z\| \le r$ each factor has $\|z - z_0\| \le r$.
--
--   **Use.** This is the analytic estimate of Baker's method in the $p$-adic setting: a function with many zeros of high order in a small disc is small on that disc. It is a tool for `NumberField.Brumer.extrapolation_step`.
--
--   **Formalization Note.** The series are `∑' k, c k * z ^ k`; the left side of the hypothesis is the Hasse derivative of order $t$, written `∑' k, (k.choose t : K) * c k * z ^ (k - t)` with natural subtraction (terms with $k < t$ are zero). All series converge because the terms tend to $0$. For $T = 0$ or $Z = \emptyset$ the bound is $\|f(z)\| \le M$. Mathlib (at this revision) has no maximum principle for non-archimedean power series; `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` gives convergence.
-- source:
--   The non-archimedean Schwarz lemma used in $p$-adic transcendence: J.-P. Serre, Dépendance d'exponentielles $p$-adiques, Séminaire Delange-Pisot-Poitou 7 (1965-66), exposé 15, as cited ("lemme de Schwarz et Mahler") in B. Rousseau, Séminaire de Théorie des Nombres de Bordeaux 1968-1969, exposé 11, p. 6. The statement here is for a series given by its coefficients, with zeros of order $T$ expressed by Hasse derivatives.

import Mathlib

theorem IsUltrametricDist.norm_tsum_mul_pow_le_of_hasseDeriv_eq_zero {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K]
    (c : ℕ → K) (hc : Filter.Tendsto c Filter.atTop (nhds 0)) (M : ℝ) (hM : ∀ k, ‖c k‖ ≤ M)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (Z : Finset K) (hZ : ∀ z ∈ Z, ‖z‖ ≤ r) (T : ℕ)
    (hzero : ∀ z ∈ Z, ∀ t < T, ∑' k : ℕ, (k.choose t : K) * c k * z ^ (k - t) = 0)
    (z : K) (hz : ‖z‖ ≤ r) :
    ‖∑' k : ℕ, c k * z ^ k‖ ≤ r ^ (T * Z.card) * M := by sorry
