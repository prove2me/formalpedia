-- Prove2me | Theorems.Thm_FourierRankQLB_theorem_5_1
-- name    : FourierRankQLB.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:47:09.89609+00:00
-- url     : https://prove2.me/theorems/9e1fa102-81da-40e5-8848-cea0502a3772
-- title:
--   Theorem 5.1 — linear membership-query lower bounds $T\ge d/250\ge n/500$
-- statement:
--   Let $n\ge2$, $d=d_n$ and $s>0$. Suppose that, for every $Q\in O(d)$ and every objective $\overline v=(d^{-1/2}\sigma,0_{\ell_n})$ with $\sigma\in\{-1,+1\}^d$, an optimizer succeeds with probability at least $2/3$ and uses at most $T$ exact membership queries to $K_{s,Q}$ per invocation. Assume either
--
--   1. the optimizer is exactly feasible in the sense of Definition 2.5 and has accuracy
--   $$
--   \varepsilon\le\frac{s}{200\sqrt{a_dd}};
--   $$
--   2. the optimizer is approximately feasible in the sense of Definition 2.6 and has tolerance
--   $$
--   \delta\le\frac{s}{200\sqrt{a_dd}\,(R_s/r_s+2)}.
--   $$
--
--   Then
--   $$
--   T\ge\frac d{250}\ge\frac n{500}.
--   $$
--   The bound holds on every nonempty finite grid fixed independently of $Q$, and for exact coherent membership on $L^2(\mathbb R^n)\otimes\mathbb C^2$.
--
--   This is the paper's main result: linear optimization over a convex body with quantum membership queries needs a number of queries linear in the dimension, at these accuracies.
--
--   **Formalization Note** On objective $\sigma$ the optimizer is a query algorithm on $L^2(Y_\sigma,\nu_\sigma)\otimes\mathbb C^2\otimes W_\sigma$ with labels $\iota_\sigma:Y_\sigma\to\mathbb R^n$ and a POVM on $\mathbb R^n$, all chosen before $Q$. The requirement $\delta<r_s$ of Definition 2.6 is not assumed, since it follows from the tolerance bound.
--
--   Differences from the source:
--
--   - generalization: every nonempty finite grid fixed independently of $Q$, possibly depending on the objective (p.32), or $L^2(\mathbb R^n)\otimes\mathbb C^2$ → any σ-finite $(Y_\sigma,\nu_\sigma)$ with a measurable labelling $\iota_\sigma$, possibly depending on $\sigma$; reason: a grid is $Y=G$ with counting measure and the inclusion, and $L^2(\mathbb R^n)$ is $Y=\mathbb R^n$ with Lebesgue measure and the identity; an empty grid carries no unit state; the proof goes through Corollary 4.5 on the disjoint union of the spaces
--   - generalization: workspace registers of $H_{alg}$, separable in Appendix A → any complex Hilbert space $W_\sigma$, possibly depending on $\sigma$; reason: separable workspaces are a special case; see Corollary 4.5
--   - encoding: an optimizer with at most $T$ queries, returning a classical vector → for each $\sigma$ a `QueryAlg` with a POVM on $\mathbb R^n$ and `(alg σ).T ≤ T`; reason: the form (15) of p.16, with the random output a POVM outcome
--   - encoding: $\sigma\in\{-1,+1\}^d$ → `Fin d → Bool` with `boolSign`; reason: a coding of the same set
--   - encoding: each query slot an allowed query or inverse query, possibly controlled by the stored history, with identity padding (p.16) → every slot applies the membership oracle itself; reason: the oracle is an involution, so its inverse is itself; a controlled or identity slot is one plain query between Q-independent unitaries that swap the answer bit with a workspace qubit in the state $|+\rangle$, which the oracle fixes; the query count is unchanged
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Theorem 5.1, p.31

import Mathlib
import Definitions.Def_FourierRankQLB_hardOracle
import Definitions.Def_FourierRankQLB_QueryAlg_outcomeProb
import Definitions.Def_FourierRankQLB_exactSuccess
import Definitions.Def_FourierRankQLB_approxSuccess
import Definitions.Def_FourierRankQLB_signObj
import Definitions.Def_FourierRankQLB_padObj
import Definitions.Def_FourierRankQLB_rs
import Definitions.Def_FourierRankQLB_Rs__d75a51

open MeasureTheory

namespace FourierRankQLB

/-- Theorem 5.1 (Linear membership-query lower bounds). Let `n ≥ 2` and `s > 0`. Suppose that, for every
`Q ∈ O(d)`, `d = d_n`, and every objective `v̄ = (d^{-1/2}σ, 0_{ℓ_n})` with `σ ∈ {-1, +1}^d`, an
optimizer succeeds with probability at least `2/3` and uses at most `T` exact membership queries to
`K_{s,Q}` per invocation, and that either (i) it is exactly feasible (Definition 2.5) with accuracy
`ε ≤ s/(200 √(a_d d))` (53), or (ii) it is approximately feasible (Definition 2.6) with tolerance
`δ ≤ s/(200 √(a_d d) (R_s/r_s + 2))` (54). Then `T ≥ d/250 ≥ n/500`. The bound holds on every nonempty
finite grid fixed independently of `Q`, and for exact coherent membership on `L²(ℝⁿ) ⊗ ℂ²`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Theorem 5.1, p. 31.

**Formalization Note.** The optimizer on objective `σ` is the query algorithm `alg σ`, on the register
`L²(Y_σ, ν_σ) ⊗ ℂ² ⊗ W_σ` with labels `ι_σ : Y_σ → ℝⁿ`, and its POVM has outcomes in `ℝⁿ`. All of this
is chosen before `Q`. The grid is `Y_σ = G`, counting measure, `ι_σ` the inclusion; the continuous
register is `Y_σ = ℝⁿ`, Lebesgue measure, `ι_σ = id`. An empty grid carries no unit state. The bound
`δ < r_s` of Definition 2.6 is not assumed: it follows from (54). -/
theorem theorem_5_1 {n : ℕ} (hn : 2 ≤ n) {s : ℝ} (hs : 0 < s)
    {Y : SignVec (dn n) → Type} [∀ σ, MeasurableSpace (Y σ)] (ν : ∀ σ, Measure (Y σ))
    [∀ σ, SigmaFinite (ν σ)] (ι : ∀ σ, Y σ → Ambient n) (hι : ∀ σ, Measurable (ι σ))
    {W : SignVec (dn n) → Type} [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] [∀ σ, CompleteSpace (W σ)]
    (alg : ∀ σ, QueryAlg (QReg (ν σ) (W σ)) (Ambient n)) (T : ℕ) (hT : ∀ σ, (alg σ).T ≤ T)
    (hopt :
      (∃ ε : ℝ, 0 < ε ∧ ε ≤ s / (200 * √(ad (dn n) * dn n)) ∧
        ∀ (Q : Od (dn n)) (σ : SignVec (dn n)),
          2 / 3 ≤ (alg σ).outcomeProb (fun _ => hardOracle (ν σ) (W σ) (ι σ) (hι σ) s Q)
            (exactSuccess (hardBody s Q) (padObj (signObj σ)) ε)) ∨
      (∃ δ : ℝ, 0 < δ ∧ δ ≤ s / (200 * √(ad (dn n) * dn n) * (Rs n s / rs n s + 2)) ∧
        ∀ (Q : Od (dn n)) (σ : SignVec (dn n)),
          2 / 3 ≤ (alg σ).outcomeProb (fun _ => hardOracle (ν σ) (W σ) (ι σ) (hι σ) s Q)
            (approxSuccess (hardBody s Q) (padObj (signObj σ)) δ))) :
    (dn n : ℝ) / 250 ≤ T ∧ (n : ℝ) / 500 ≤ (dn n : ℝ) / 250 := by sorry

end FourierRankQLB
