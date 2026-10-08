-- Prove2me | Theorems.Thm_MatteBon_entropy_convPow_le_and_asymptoticEntropy_eq_zero
-- name    : MatteBon.entropy_convPow_le_and_asymptoticEntropy_eq_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T14:44:39.2245+00:00
-- url     : https://prove2.me/theorems/1ef5a841-ce44-4a92-a213-a39c3cd5e4d7
-- title:
--   Matte Bon, Theorem 1.2 — random walks on the topological full group of a subshift of complexity below n² have zero entropy
-- statement:
--   Let $\Sigma \subseteq A^{\mathbf Z}$ be a subshift over a finite alphabet $A$, with shift $\tau$, whose non-periodic points are dense. Suppose that there are $\alpha < 2$ and $C$ such that the complexity satisfies $\rho(n) \le C n^\alpha$ for all $n \ge 1$. Let $\mu$ be a finitely supported symmetric probability measure on the topological full group $[[\tau]]$. Then there is $C'$ such that for all $n \ge 2$
--   $$H(\mu^{*n}) \le C' n^{\alpha/2} (\log n)^{1+\alpha/2},$$
--   and the random-walk entropy $h(\mu) = \lim_n H(\mu^{*n})/n$ is $0$.
--
--   Matte Bon, p. 3: “Theorem 1.2. Let $(\tau, \Sigma)$ be a subshift, and assume that the set of non-periodic points is dense in $\Sigma$. Suppose that there exists $\alpha < 2$ such that the complexity $\rho$ of $\Sigma$ satisfies $\rho(n) \le Cn^\alpha$. Then for every finitely supported symmetric probability measure $\mu$ on $[[\tau]]$ the random walk entropy vanishes. More precisely, there exists a constant $C > 0$ such that $H(\mu^{*n}) \le Cn^{\alpha/2}(\log n)^{1+\alpha/2}$.”
--
--   *Formalization note.* The complexity bound is assumed for $n \ge 1$: at $n = 0$ the empty word gives $\rho(0) = 1 > C \cdot 0^\alpha$ for $\alpha > 0$, which would force $\Sigma$ to be empty. The entropy bound is stated for $n \ge 2$, where $\log n > 0$. A point is non-periodic when no nonzero power of $\tau$ fixes it. Matte Bon calls a subshift a Cantor system (p. 2); the subshift is not assumed to be a Cantor space here, which makes the statement stronger. Entropy, convolution powers and the asymptotic entropy are those of the Erschler–Zheng bundle; by the Kaimanovich–Vershik entropy criterion (`KaimanovichVershik.not_hasNontrivialPoissonBoundary_iff_asymptoticEntropy_eq_zero`), zero entropy means that $([[\tau]], \mu)$ has the Liouville property.
-- source:
--   Matte Bon, N., Subshifts with slow complexity and simple groups with the Liouville property, Geom. Funct. Anal. 24 (2014) 1637–1659, https://doi.org/10.1007/s00039-014-0293-4 (arXiv:1402.2234v2, whose page numbers are used), p. 3, Theorem 1.2

import Mathlib
import Definitions.Def_CantorSystems
import Definitions.Def_ErschlerZheng_Walks

open CantorSystems ErschlerZheng

namespace MatteBon

theorem entropy_convPow_le_and_asymptoticEntropy_eq_zero
    {A : Type*} [Finite A] [TopologicalSpace A] [DiscreteTopology A] (S : Subshift ℤ A)
    (hS : Dense {x : S | ∀ k : ℤ, k +ᵥ x = x → k = 0})
    {α C : ℝ} (hα : α < 2)
    (hρ : ∀ n : ℕ, 1 ≤ n → (wordComplexity (S : Set (ℤ → A)) n : ℝ) ≤ C * (n : ℝ) ^ α)
    (μ : topologicalFullGroup ℤ S → ℝ) (hfin : (Function.support μ).Finite)
    (hμ : IsProbability μ) (hsymm : IsSymmetric μ) :
    (∃ C' : ℝ, ∀ n : ℕ, 2 ≤ n →
      entropy (convPow μ n) ≤ C' * (n : ℝ) ^ (α / 2) * Real.log n ^ (1 + α / 2)) ∧
    asymptoticEntropy μ = 0 := by
  sorry

end MatteBon
