-- Prove2me | Theorems.Thm_IRLSM_Convergence_theorem_6_11
-- name    : IRLSM.Convergence.theorem_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:29.347796+00:00
-- url     : https://prove2.me/theorems/2b5a023a-aade-459d-92c0-39900f5e94d3
-- title:
--   Theorem 6.11 — IRLS-M converges to the nuclear norm minimizer under the strong rank null space property
-- statement:
--   Consider the IRLS-M algorithm with parameters $\gamma=1/n$ and $K\in\mathbb N$, for a surjective linear map $\mathcal S:\mathbb R^{n\times p}\to\mathbb R^m$ and data $\mathscr M\in\mathbb R^m$. Let $(X^\ell,\varepsilon_\ell)$ be a run. Then:
--
--   1. If $\mathcal S$ satisfies the strong rank null space property of order $K$ and $\lim_{\ell\to\infty}\varepsilon_\ell=0$, then $X^\ell$ converges to a matrix $\bar X$ of rank at most $K$ with $\mathcal S(\bar X)=\mathscr M$, and $\bar X$ is the unique nuclear norm minimizer: $\|\bar X\|_*<\|Y\|_*$ for every $Y\ne\bar X$ with $\mathcal S(Y)=\mathscr M$.
--   2. If $\lim_{\ell\to\infty}\varepsilon_\ell=\varepsilon>0$, then every subsequence of $(X^\ell)$ has a convergent subsequence; every accumulation point $\tilde X$ of $(X^\ell)_{\ell\ge1}$ is a minimizer of $\mathcal J_\varepsilon$ subject to $\mathcal S(X)=\mathscr M$; and if this minimizer is unique, the whole sequence converges to it. If in addition $\mathcal S$ satisfies the SRNSP of order $K$ with constant $\eta<1-\frac{2}{K-2}$, then every accumulation point $\bar X$ satisfies, for every $X$ with $\mathcal S(X)=\mathscr M$ and every $k<K-\frac{2\eta}{1-\eta}$,
--   $$\|X-\bar X\|_*\le\Lambda\,\rho_k(X)_*,\qquad \Lambda=\frac{4(1+\eta)^2}{(1-\eta)^2\big((K-k)(1-\eta)-2\eta\big)}+\frac{2(1+\eta)}{1-\eta}.$$
--   3. If $\mathcal S$ satisfies the SRNSP of order $K$ with constant $\eta<1-\frac{2}{K-2}$ and some $X$ of rank at most $k$ satisfies $\mathcal S(X)=\mathscr M$ (with $k<K-\frac{2\eta}{1-\eta}$), then $\lim_\ell\varepsilon_\ell=0$.
--
--   This is the main result of the paper: IRLS-M recovers low-rank matrices exactly, and approximately low-rank matrices stably, whenever the measurement map has the strong rank null space property.
--
--   **Formalization Note** Matrices are real ($n\times p$, with the paper's standing assumption $n\le p$ where $n\times n$ objects occur); the measurement map is $\mathcal S(X)_l=\langle A_l,X\rangle$ for measurement matrices $A_1,\dots,A_m$, so $\mathcal S^*$ is $u\mapsto\sum_l u_lA_l$ and $\langle\cdot,\cdot\rangle$ is the trace inner product. The run is the relation `IsRun` (any minimizer at each step; $\varepsilon_j=0$ after a stop; $X^0$ unconstrained). The nonincreasing, nonnegative sequence $\varepsilon_\ell$ always converges, and "$\varepsilon=0$" in item 3 is $\varepsilon_\ell\to0$. Accumulation points are cluster points of the sequence. In item 3, $k$ ranges over the same $k<K-2\eta/(1-\eta)$ as in item 2, which its proof uses. The condition $\eta<1-2/(K-2)$ is kept literally in $\mathbb R$; for $K\le2$ it is implied by $\eta<1$, part of the SRNSP.
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Theorem 6.11, pp. 20–21

import Mathlib
import Definitions.Def_IRLSM_Convergence_Algorithm

open HighDimStat.MatrixRank Matrix Filter Topology

namespace IRLSM.Convergence

/-- **Theorem 6.11.** Consider the IRLS-M algorithm with `γ = 1/n` and `K ∈ ℕ`, for a surjective
`S : M_{n×p} → ℝ^m` and data `𝓜`. The iterates `(X^ℓ)` satisfy:
(i) if `S` has the SRNSP of order `K` and `ε_ℓ → 0`, then `X^ℓ` converges to a matrix `X̄` of rank
at most `K` with `S(X̄) = 𝓜`, which is the unique nuclear norm minimizer;
(ii) if `ε_ℓ → ε > 0`, then every subsequence has a convergent subsequence, every accumulation
point is a minimizer of `𝒥_ε` subject to `S(X) = 𝓜`, the whole sequence converges if this
minimizer is unique; and if `S` has the SRNSP of order `K` with constant `η < 1 − 2/(K − 2)`, every
accumulation point `X̄` satisfies `‖X − X̄‖_* ≤ Λ ρ_k(X)_*` for every feasible `X` and every
`k < K − 2η/(1 − η)`;
(iii) under that SRNSP, if some feasible matrix has rank at most `k`, then `ε = 0`.

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Theorem 6.11, pp. 20–21.

Formalization Notes: real matrices; `S(X)_l = ⟨A_l, X⟩`; `n ≤ p` is the page's standing assumption
(p. 4); the run is `IsRun` (`X 0` free, `ε_j = 0` after a stop). `ε_ℓ` is nonincreasing and
nonnegative, so it always converges; "`lim ε_ℓ = ε`" is `Tendsto ε atTop (𝓝 e)`, and (iii)'s
"`ε = 0`" is `Tendsto ε atTop (𝓝 0)`. Accumulation points are `MapClusterPt`. In (ii)(d) the
page's `X` is `Y` and `X̄` is `Xt`; `Λ` is `Lambda η K k`. In (iii) `k` ranges over the same
`k < K − 2η/(1 − η)` as in (ii), which its proof uses. The condition `η < 1 − 2/(K − 2)` is kept
literally in `ℝ` (for `K ≤ 2` it is implied by `η < 1`, part of the SRNSP). The goal's "unique
nuclear norm minimizer" is the strict inequality `‖X̄‖_* < ‖Y‖_*` for every feasible `Y ≠ X̄`. -/
theorem theorem_6_11 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (M : Fin m → ℝ) (K : ℕ)
    (X : ℕ → Matrix (Fin n) (Fin p) ℝ) (ε : ℕ → ℝ) (hnp : n ≤ p)
    (hS : Function.Surjective (observationOp A)) (hrun : IsRun A M K (1 / (n : ℝ)) X ε) :
    -- (i)
    ((∃ η : ℝ, SRNSP A K η) → Tendsto ε atTop (𝓝 0) →
      ∃ Xbar : Matrix (Fin n) (Fin p) ℝ, Tendsto X atTop (𝓝 Xbar) ∧ Xbar.rank ≤ K ∧
        observationOp A Xbar = M ∧
        ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Y ≠ Xbar →
          nuclearNorm Xbar < nuclearNorm Y) ∧
    -- (ii)
    (∀ e : ℝ, 0 < e → Tendsto ε atTop (𝓝 e) →
      (∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∃ L : Matrix (Fin n) (Fin p) ℝ, Tendsto (X ∘ φ ∘ ψ) atTop (𝓝 L)) ∧
      (∀ Xt : Matrix (Fin n) (Fin p) ℝ, MapClusterPt Xt atTop X →
        observationOp A Xt = M ∧
          ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Jeps e Xt ≤ Jeps e Y) ∧
      (∀ Xm : Matrix (Fin n) (Fin p) ℝ,
        (observationOp A Xm = M ∧
          ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Jeps e Xm ≤ Jeps e Y) →
        (∀ Z : Matrix (Fin n) (Fin p) ℝ, observationOp A Z = M →
          (∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M → Jeps e Z ≤ Jeps e Y) →
            Z = Xm) →
        Tendsto X atTop (𝓝 Xm)) ∧
      (∀ η : ℝ, SRNSP A K η → η < 1 - 2 / ((K : ℝ) - 2) →
        ∀ Xt : Matrix (Fin n) (Fin p) ℝ, MapClusterPt Xt atTop X →
          ∀ Y : Matrix (Fin n) (Fin p) ℝ, observationOp A Y = M →
            ∀ k : ℕ, (k : ℝ) < K - 2 * η / (1 - η) →
              nuclearNorm (Y - Xt) ≤ Lambda η K k * rho k Y)) ∧
    -- (iii)
    (∀ η : ℝ, SRNSP A K η → η < 1 - 2 / ((K : ℝ) - 2) →
      ∀ k : ℕ, (k : ℝ) < K - 2 * η / (1 - η) →
        (∃ X₀ : Matrix (Fin n) (Fin p) ℝ, X₀.rank ≤ k ∧ observationOp A X₀ = M) →
          Tendsto ε atTop (𝓝 0)) := by sorry

end IRLSM.Convergence
