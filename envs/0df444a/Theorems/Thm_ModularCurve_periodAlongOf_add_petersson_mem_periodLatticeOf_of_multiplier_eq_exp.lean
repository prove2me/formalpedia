-- Prove2me | Theorems.Thm_ModularCurve_periodAlongOf_add_petersson_mem_periodLatticeOf_of_multiplier_eq_exp
-- name    : ModularCurve.periodAlongOf_add_petersson_mem_periodLatticeOf_of_multiplier_eq_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/2278315e-a803-5b55-a989-e1d3fe075e65
-- title:
--   Abel-type theorem: periods plus Petersson term lie in Λ_Γ
-- statement:
--   Let $\Gamma\le SL_2(\mathbb Z)$ be of finite index with $-1\in\Gamma$, let $c:\mathfrak H\to\mathbb Z$ be finitely supported, let $F:\mathfrak H\to\mathbb C$ and let $k$ be a cusp form of weight $2$ on $\Gamma$. Assume: (i) for each $\tau\in\mathfrak H$ the function $z\mapsto F(\mathrm{ofComplex}\,z)$ is meromorphic at $\tau$; (ii) for all $\gamma\in\Gamma$ and $\tau$, $F(\gamma\tau)=\exp\bigl(2\pi i\,\operatorname{Re}(\mathrm{periodOf}\,\Gamma\,\gamma)(k)\bigr)F(\tau)$, where $(\mathrm{periodOf}\,\Gamma\,\gamma)(f)=\int_0^1 f(\text{segment from }i\text{ to }\gamma i)(\gamma i-i)\,dt$; (iii) for each $\sigma\in SL_2(\mathbb Z)$ the function $\tau\mapsto F(\sigma\tau)$ tends to some non-zero limit as $\operatorname{Im}\tau\to\infty$; (iv) for each $\tau$ the meromorphic order of $z\mapsto F(\mathrm{ofComplex}\,z)$ at $\tau$ is an integer $n$ with $2n=\#\mathrm{Stab}_\Gamma(\tau)\cdot\sum_{\tau'}c(\tau')$, the sum over $\tau'$ in the support of $c$ with $\tau'$ in the $\Gamma$-orbit of $\tau$. Then there is an element $\Lambda$ of the period lattice of $\Gamma$, i.e. of the $\mathbb Z$-span of the functionals $\mathrm{periodOf}\,\Gamma\,\gamma$ inside the $\mathbb C$-dual of $\mathrm{CuspForm}\,\Gamma\,2$, such that for every weight-$2$ cusp form $g$ on $\Gamma$,
--   $$\sum_{\tau}c(\tau)\,(\mathrm{periodAlongOf}\,\Gamma\,i\,\tau)(g)+i\int_{\mathcal F_\Gamma}\mathrm{petersson}\,2\,k\,g=\Lambda(g),$$
--   where $\mathcal F_\Gamma=\bigcup_{q\in SL_2(\mathbb Z)/\Gamma}(q_{\mathrm{out}})^{-1}\cdot\mathcal D$ is the union of translates of the standard fundamental domain by the inverses of chosen coset representatives.
--
--   This is the necessity half of an Abel-type reciprocity theorem on the modular curve $\Gamma\backslash\mathfrak H$ with a harmonic twist: a divisor whose multiplicities are realised by the orders of a function with the exponential multiplier attached to $k$ has its Abel–Jacobi functional, corrected by $i$ times the weight-$2$ Petersson pairing against $k$, congruent to zero modulo the period lattice. The proof goes through the construction of a chain with the prescribed boundary and the fact that chains with vanishing boundary give period-lattice elements; the converse implication is recorded in [`ModularCurve.multiplier_eq_exp_of_periodAlongOf_add_petersson_mem_periodLatticeOf`](thm.html#ModularCurve.multiplier_eq_exp_of_periodAlongOf_add_petersson_mem_periodLatticeOf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodAlongOf_add_petersson_mem_periodLatticeOf_of_multiplier_eq_exp.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology
open Classical in

theorem ModularCurve.periodAlongOf_add_petersson_mem_periodLatticeOf_of_multiplier_eq_exp
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (k : CuspForm Γ 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, ∃ n : ℤ,
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
        2 * n = (Nat.card (MulAction.stabilizer Γ τ) : ℤ) *
          c.sum (fun τ' m =>
            if ∃ γ : Γ, (γ : SL(2, ℤ)) • τ' = τ then m else 0)) :
    ∃ Λ ∈ ModularCurve.periodLatticeOf Γ, ∀ g : CuspForm Γ 2,
      (c.sum fun τ n => n • ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ) g +
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
          UpperHalfPlane.petersson 2 ⇑k ⇑g τ) = Λ g := by sorry
