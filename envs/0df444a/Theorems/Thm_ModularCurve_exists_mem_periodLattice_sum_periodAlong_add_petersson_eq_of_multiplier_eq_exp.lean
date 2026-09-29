-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_periodLattice_sum_periodAlong_add_petersson_eq_of_multiplier_eq_exp
-- name    : ModularCurve.exists_mem_periodLattice_sum_periodAlong_add_petersson_eq_of_multiplier_eq_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/e3a77f65-a4e4-5744-a1e3-be744786b866
-- title:
--   Reciprocity law on X₀(N): divisor periods and Petersson integral
-- statement:
--   Fix $N \ge 1$, a function $F : \mathbb{H} \to \mathbb{C}$ and a weight‑$2$ cusp form $k$ for $\Gamma_0(N)$. Assume: (i) the function $z \mapsto F(\mathrm{ofComplex}\,z)$ is meromorphic at every point $\tau$ of the upper half‑plane; (ii) for all $\gamma \in \Gamma_0(N)$ and all $\tau$, $F(\gamma \cdot \tau) = \exp\!\big(2\pi i\,\operatorname{Re}(\mathrm{period}\,N\,\gamma\,k)\big)\,F(\tau)$, where $\mathrm{period}\,N\,\gamma$ is the functional sending a weight‑$2$ cusp form $g$ to $\int_0^1 g(\text{segment from } i \text{ to } \gamma\cdot i \text{ at } t)\,(\gamma\cdot i - i)\,dt$, i.e. $\int g\,d\tau$ along the straight segment from $i$ to $\gamma \cdot i$; (iii) for every $\sigma \in SL_2(\mathbb{Z})$ the function $\tau \mapsto F(\sigma\cdot\tau)$ tends to a non‑zero limit as $\operatorname{Im}\tau \to \infty$. Let $S$ be a finite set of points of $\mathbb{H}$ and $n : \mathbb{H} \to \mathbb{Z}$ be such that the meromorphic order of $F$ at each $s \in S$ equals $n(s)$, such that distinct points of $S$ are $\Gamma_0(N)$‑inequivalent, and such that every point where the order of $F$ is non‑zero is $\Gamma_0(N)$‑equivalent to a point of $S$. The conclusion asserts the existence of $\Lambda$ in the period lattice of level $N$ — the $\mathbb{Z}$‑span inside the dual of $S_2(\Gamma_0(N))$ of the functionals $\mathrm{period}\,N\,\gamma$, $\gamma \in \Gamma_0(N)$ — such that for every weight‑$2$ cusp form $g$ for $\Gamma_0(N)$,
--   $$\sum_{s \in S} \frac{2\,n(s)}{\#\mathrm{Stab}_{\Gamma_0(N)}(s)} \int_{i}^{s} g\,d\tau \;+\; i \int_{\mathcal{F}} \mathrm{petersson}\,2\,k\,g \;+\; \Lambda(g) = 0,$$
--   where the first integral is taken along the straight segment from $i$ to $s$, and $\mathcal{F}$ is the fundamental set $\bigcup_{q \in SL_2(\mathbb{Z})/\Gamma_0(N)} (\mathrm{out}\,q)^{-1} \cdot \mathcal{D}$ obtained from the standard fundamental domain $\mathcal{D}$ of $SL_2(\mathbb{Z})$ and chosen coset representatives.
--
--   This is Riemann's bilinear relation (reciprocity law) on the compact Riemann surface $X_0(N)$, pairing the closed $\Gamma_0(N)$‑invariant form attached to $d\log F$, whose residues are the orders of $F$ and whose periods lie in $2\pi i \mathbb{Z}$, against the holomorphic differentials $g\,d\tau$; the divisor contribution appears as segment periods from $i$, and the Petersson term as an integral over the fundamental set. It is used by [`ModularCurve.exists_chain_periodAlong_add_petersson_eq_zero_of_multiplier_eq_exp`](thm.html#ModularCurve.exists_chain_periodAlong_add_petersson_eq_zero_of_multiplier_eq_exp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_periodLattice_sum_periodAlong_add_petersson_eq_of_multiplier_eq_exp.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

theorem ModularCurve.exists_mem_periodLattice_sum_periodAlong_add_petersson_eq_of_multiplier_eq_exp
    {N : ℕ} [NeZero N]
    (F : ℍ → ℂ) (k : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ s ∈ S, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (s : ℂ) = (n s : WithTop ℤ))
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hcov : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ 0 →
      ∃ s ∈ S, ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • s = τ) :
    ∃ Λ ∈ ModularCurve.periodLattice N,
      ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        (∑ s ∈ S, (2 * (n s : ℂ) /
            (Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) s) : ℂ)) *
              ModularCurve.periodAlong N UpperHalfPlane.I s g) +
          Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
            (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 k g τ) +
          Λ g = 0 := by sorry
