-- Prove2me | Theorems.Thm_LewisTorczon_BoundPS_theorem_2_2
-- name    : LewisTorczon.BoundPS.theorem_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:43:16.746741+00:00
-- url     : https://prove2.me/theorems/ff82e15a-6d76-45dc-ae0d-a610567c6f74
-- title:
--   Theorem 2.2 — the iterates lie on the lattice $x_0+\beta^{r_{LB}}\alpha^{-r_{UB}}\Delta_0 B\,\mathbb Z^n$
-- statement:
--   Consider a run $x_k,\Delta_k$ of the generalized pattern search method for bound constrained problems, with basis matrix $B$ and expansion/contraction base $\tau\in\mathbb Q$, $\tau>1$. Write $\tau=\beta/\alpha$ with $\alpha,\beta\in\mathbb N$ relatively prime. Because the update of $\Delta_k$ multiplies by integer powers of $\tau$, we can write $\Delta_k=\tau^{r_k}\Delta_0$ with $r_k\in\mathbb Z$. For $N\ge1$ put
--   $$r_{LB}=\min_{0\le k<N} r_k,\qquad r_{UB}=\max_{0\le k<N} r_k .$$
--   Then there are integer vectors $z_0,\dots,z_{N-1}\in\mathbb Z^n$ such that
--   $$x_N=x_0+\bigl(\beta^{r_{LB}}\alpha^{-r_{UB}}\bigr)\Delta_0\,B\sum_{k=0}^{N-1}z_k .$$
--
--   The theorem says that the iterates are confined to a translated integer lattice whose mesh size is controlled by the extreme step lengths; combined with compactness of the level set, it forces the iterates to take only finitely many values when $\Delta_k$ is bounded away from zero, which drives the proof that $\liminf_k\Delta_k=0$.
--
--   **Formalization Note** The sequence $r_k$ is taken as a hypothesis $\Delta_k=\tau^{r_k}\Delta_0$ for all $k$ (it is uniquely determined, since $\tau>1$ and $\Delta_0>0$). $r_{LB}$ and $r_{UB}$ are pinned to the minimum and maximum over $0\le k<N$, as identified on p. 10 of the paper; the case $N=0$ is excluded because these are undefined for an empty range (for $N=0$ the statement is trivial with an empty sum). The paper quotes this result from Torczon (1997), Theorem 3.2.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 5, Theorem 2.2 (Theorem 3.2 from [14]), eq. (5); r_LB, r_UB as identified on p. 10 (proof of Theorem 4.5)

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Theorem 2.2** (Theorem 3.2 of Torczon 1997), p. 5, eq. (5), with `r_LB`, `r_UB` as identified
on p. 10: write `τ = β/α` with `α, β ∈ ℕ` coprime, and `Δ_k = τ^{r_k} Δ_0` with `r_k ∈ ℤ`. For
every `N ≥ 1` there are integer vectors `z_0, …, z_{N-1}` with
`x_N = x_0 + (β^{r_LB} α^{-r_UB}) Δ_0 B Σ_{k=0}^{N-1} z_k`, where
`r_LB = min_{0 ≤ k < N} r_k` and `r_UB = max_{0 ≤ k < N} r_k`. -/
theorem theorem_2_2 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) (α β : ℕ) (hα : 0 < α) (hcop : Nat.Coprime α β)
    (hτ : P.τ = (β : ℚ) / (α : ℚ)) (r : ℕ → ℤ)
    (hr : ∀ k, R.Δ k = (P.τ : ℝ) ^ r k * R.Δ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∃ z : ℕ → (Fin n → ℤ),
      R.x N = R.x 0 +
        ((β : ℝ) ^ ((Finset.range N).inf' (Finset.nonempty_range_iff.mpr (by omega)) r) *
            (α : ℝ) ^ (-((Finset.range N).sup' (Finset.nonempty_range_iff.mpr (by omega)) r)) *
            R.Δ 0) •
          WithLp.toLp 2 (P.B.mulVec (fun i => (((∑ k ∈ Finset.range N, z k i : ℤ)) : ℝ))) := by sorry

end LewisTorczon.BoundPS
