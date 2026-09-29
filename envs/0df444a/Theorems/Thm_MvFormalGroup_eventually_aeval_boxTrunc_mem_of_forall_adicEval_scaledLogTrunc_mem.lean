-- Prove2me | Theorems.Thm_MvFormalGroup_eventually_aeval_boxTrunc_mem_of_forall_adicEval_scaledLogTrunc_mem
-- name    : MvFormalGroup.eventually_aeval_boxTrunc_mem_of_forall_adicEval_scaledLogTrunc_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/2757d827-493d-5bd5-a90c-574bb68905d9
-- title:
--   Box truncations of the logarithm lie in p^vY at w'
-- statement:
--   Let $\mathcal O$ be a commutative ring, $p$ a prime whose image in $\mathcal O$ is a non-zero-divisor, and $F$ a $d$-dimensional commutative formal group law over $\mathcal O$: a $d$-tuple $F_i$ of power series in the variables indexed by $\mathrm{Fin}\,d\sqcup\mathrm{Fin}\,d$ with vanishing constant term, with $\mathrm{coeff}_{e_{\mathrm{inl}(j)}}F_i=\mathrm{coeff}_{e_{\mathrm{inr}(j)}}F_i=\delta_{ij}$, satisfying associativity, and invariant under interchanging the two blocks of variables. Let $F_p=(F_{p,i})$ be a $d$-tuple of power series in the same variables with zero constant terms such that $\mathrm{coeff}_m(F_{p,i})\cdot p=p^{|m|}\,\mathrm{coeff}_m(F_i)$ for all $m\neq 0$, and let $\varphi=(\varphi_i)$ be a $d$-tuple of power series in $d$ variables with zero constant terms such that: for every $N$ and $i$ all but finitely many coefficients of $\varphi_i$ lie in $(p^N)$; $\varphi_i\circ F_p=\varphi_i(X_{\mathrm{inl}})+\varphi_i(X_{\mathrm{inr}})$ for all $i$; and $(m_j+1)\,\mathrm{coeff}_{m+e_j}(\varphi_i)\in(p^{|m|})$ for all $i,j,m$. Fix $v\in\mathbb N$ and a commutative $\mathcal O$-algebra $Y$ that is finite and free as an $\mathcal O$-module and complete for the $(p)$-adic topology. Let $\hat y\in Y^d$ have all coordinates in the radical of $(p)$, and let $w'\in Y^d$ satisfy $[p^v]_F(\hat y)_j=p\,w'_j$, where $[n]_F$ is the $n$-fold iterate of $F$ defined by $[0]_F=0$, $[n+1]_F{}_i=F_i([n]_F,X)$ and the value at $\hat y$ is the $p$-adically convergent evaluation. Assume there is $N_0$ such that for every $N\ge N_0$, every $i$ and every power series $G$ in $d$ variables over $\mathcal O$ whose coefficients satisfy $\mathrm{coeff}_mG=p^{N-|m|}\mathrm{coeff}_m(\varphi_i)$ when $|m|\le N$, and, when $|m|>N$, either $\mathrm{coeff}_mG\cdot p^{|m|-N}=\mathrm{coeff}_m(\varphi_i)$ or $\mathrm{coeff}_mG=0$ with $p^{|m|-N}\nmid\mathrm{coeff}_m(\varphi_i)$, one has $G(\hat y)\in(p^N)$. Then there is $n_0$ such that for all $n\ge n_0$, all $i$, and every polynomial $P\in\mathcal O[X_1,\dots,X_d]$ whose coefficient at $m$ equals $\mathrm{coeff}_m(\varphi_i)$ when $m_j<n$ for all $j$ and $0$ otherwise, the value $P(w')$ lies in the ideal $(p^v)$ of $Y$.
--
--   This is the bookkeeping link between Fontaine's condition on the ghost components of logarithm covectors at a point $\hat y$ and the integrality hypothesis required to evaluate the logarithm $\varphi$ at the divided point $w'$: it converts vanishing modulo $p^N$ of all scaled truncations of $\varphi_i$ at $\hat y$ into $\varphi_i(w')\in p^vY$, read off from the box truncations of $\varphi_i$. It is used in the construction of algebra homomorphisms out of deformation rings, in [`Deformation.exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_mvFormalGroup`](thm.html#Deformation.exists_algHom_baseChange_eq_of_forall_map_mem_fontaineKer_of_mvFormalGroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_eventually_aeval_boxTrunc_mem_of_forall_adicEval_scaledLogTrunc_mem.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPowerSeries

universe u w

theorem MvFormalGroup.eventually_aeval_boxTrunc_mem_of_forall_adicEval_scaledLogTrunc_mem
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))

    (hφint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * (φ i).coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (v : ℕ)
    (Y : Type w) [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
    [IsAdicComplete (Ideal.span {(p : Y)}) Y]
    (ŷ : Fin d → Y) (hŷ : ∀ j, ŷ j ∈ (Ideal.span {(p : Y)}).radical)
    (w' : Fin d → Y)
    (hw' : ∀ j, MvFormalGroup.adicEval (Ideal.span {(p : Y)}) ŷ (F.nthSeries (p ^ v) j) = (p : Y) * w' j)
    (hG : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (i : Fin d) (G : MvPowerSeries (Fin d) 𝓞),
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ N → G.coeff m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
        (N < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
          (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m))) →
      MvFormalGroup.adicEval (Ideal.span {(p : Y)}) ŷ G ∈ Ideal.span {(p : Y) ^ N}) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (i : Fin d) (P : MvPolynomial (Fin d) 𝓞),
      (∀ m : Fin d →₀ ℕ, P.coeff m = if ∀ j, m j < n then (φ i).coeff m else 0) →
        MvPolynomial.aeval w' P ∈ Ideal.span {(p : Y) ^ v} := by sorry
