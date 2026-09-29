-- Prove2me | Theorems.Thm_MvFormalGroup_coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope
-- name    : MvFormalGroup.coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/01a8541f-9b10-5160-b17d-babd6524f014
-- title:
--   Far Witt components of the logarithm lie in (p)+(X)^E
-- statement:
--   Let $\mathcal{O}$ be a commutative ring and $p$ a prime such that $p$ is a non-zero-divisor in $\mathcal{O}$, equipped with an $\mathcal{O}$-algebra structure on $\mathbb{Z}/p$ whose structure map has kernel exactly the ideal $(p)$ of $\mathcal{O}$. Let $d\in\mathbb{N}$ and let $\varphi_i\in\mathcal{O}[[X_0,\dots,X_{d-1}]]$ be a multivariate power series satisfying two hypotheses: a log-integrality condition, namely that for every coordinate $j$ and every exponent $m$ one has $(m_j+1)\,\mathrm{coeff}_{m+e_j}(\varphi_i)\in\big(p^{|m|}\big)$, where $|m|$ is the total degree of $m$; and a slope bound, namely that for fixed naturals $A<B$ and $C$ and every $m\neq 0$ one has $\mathrm{coeff}_m(\varphi_i)\in\big(p^{(|m|-1)-\lfloor A\lfloor\log_p|m|\rfloor/B\rfloor-C}\big)$, all subtractions being truncated. Then for every $E\in\mathbb{N}$ there exists $n_2\in\mathbb{N}$, depending on the above data but not on what follows, such that: for every $M\in\mathbb{N}$ and every family $c$ of elements of $\mathcal{O}$ indexed by exponents $m$ with $c_m=p^{M-|m|}\mathrm{coeff}_m(\varphi_i)$ when $|m|\le M$, and with, when $|m|>M$, either $c_m\,p^{|m|-M}=\mathrm{coeff}_m(\varphi_i)$ or else $c_m=0$ and $p^{|m|-M}\nmid\mathrm{coeff}_m(\varphi_i)$, and for every Witt vector $\ell\in W(\mathcal{O}[[X_0,\dots,X_{d-1}]])$ at $p$ whose ghost components satisfy $\mathrm{coeff}_{m'}\big(w_n(\ell)\big)=c_{p^{M-1-n}m'}$ for all $n<M$ and all $m'$, one has $\ell_j\in (p)+(X_0,\dots,X_{d-1})^E$ for every $j$ with $j+n_2<M$.
--
--   This is the coordinate-free form of the statement that the far components of the Witt (Dwork) covector attached to the logarithm of a formal group tend to zero: given any prescribed depth $E$ in the $(p,X)$-adic filtration, all components of index bounded away from the truncation length $M$ by a constant $n_2$ lie in $(p)+(X)^E$. It is used in the passage from logarithm covectors to deformations, via [`Deformation.map_coeff_mem_span_of_forall_coeff_ghostComponent_eq_logCovector`](thm.html#Deformation.map_coeff_mem_span_of_forall_coeff_ghostComponent_eq_logCovector).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MvPowerSeries

universe u

theorem MvFormalGroup.coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (φi : MvPowerSeries (Fin d) 𝓞)
    (hφint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * φi.coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (A B C : ℕ) (hAB : A < B)
    (hslope : ∀ m : Fin d →₀ ℕ, m ≠ 0 →
      φi.coeff m ∈ Ideal.span {(p : 𝓞) ^ ((m.degree - 1) - (A * Nat.log p m.degree) / B - C)})
    (E : ℕ) :
    ∃ n₂ : ℕ, ∀ (M : ℕ) (c : (Fin d →₀ ℕ) → 𝓞),
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ M → c m = (p : 𝓞) ^ (M - m.degree) * φi.coeff m) ∧
        (M < m.degree → c m * (p : 𝓞) ^ (m.degree - M) = φi.coeff m ∨
          (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ φi.coeff m))) →
      ∀ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞),
        (∀ n : ℕ, n < M → ∀ m' : Fin d →₀ ℕ,
          (WittVector.ghostComponent n ℓ).coeff m' = c (p ^ (M - 1 - n) • m')) →
        ∀ j : ℕ, j + n₂ < M →
          ℓ.coeff j ∈ Ideal.span {(p : MvPowerSeries (Fin d) 𝓞)} ⊔
            (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞))) ^ E := by sorry
