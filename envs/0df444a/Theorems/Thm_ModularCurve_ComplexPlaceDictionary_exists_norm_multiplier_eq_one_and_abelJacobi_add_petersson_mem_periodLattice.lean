-- Prove2me | Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice
-- name    : ModularCurve.ComplexPlaceDictionary.exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/393b82aa-dd49-5b22-976f-35c1e579bfa9
-- title:
--   Unitary multiplier function for a degree-zero divisor on X₀(N)
-- statement:
--   Fix $N \ge 1$ and a structure $D$ of type [`ModularCurve.ComplexPlaceDictionary N`](def/ModularCurve_ComplexPlaceDictionary.html#L28), i.e. an assignment $\tau \mapsto D.\mathrm{pt}\,\tau$ of places of the field $\mathbb{C}$-base change `laurentBaseChange ℂ (modularFunctionFieldFull N)` of the level-$N$ modular function field, together with positive integers $D.\mathrm{ramification}\,\tau$, such that $D.\mathrm{pt}$ is invariant under the action of $\Gamma_0(N)$ on $\mathbb{H}$, the valuation subring of $D.\mathrm{pt}\,\tau$ consists exactly of those field elements whose realisation as a function on $\mathbb{H}$ is bounded near $\tau$ on the punctured neighbourhood filter, and for every non-zero $x$ the meromorphic order at $\tau$ of the realisation of $x$ equals $D.\mathrm{ramification}\,\tau$ times the valuation $\mathrm{ord}_{D.\mathrm{pt}\,\tau}(x)$. Let $c : \mathbb{H} \to \mathbb{Z}$ be finitely supported and assume the pushforward divisor $D_*(c) = \mathrm{mapDomain}\,D.\mathrm{pt}\,c$ has degree zero, the degree being $\sum_v c_v \deg v$. Then there are a function $F : \mathbb{H} \to \mathbb{C}$, a function $\chi : \Gamma_0(N) \to \mathbb{C}$ and a cusp form $f$ of weight $2$ on $\Gamma_0(N)$ such that: $z \mapsto F(\mathrm{ofComplex}\,z)$ is meromorphic at every point of $\mathbb{H}$; $F(\gamma \tau) = \chi(\gamma) F(\tau)$ for all $\gamma \in \Gamma_0(N)$ and $\tau$; $\|\chi(\gamma)\| = 1$ for all $\gamma$; for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ the function $\tau \mapsto F(\sigma \tau)$ tends to a non-zero limit as $\mathrm{Im}\,\tau \to \infty$; the meromorphic order of $F$ at each $\tau$ equals $D.\mathrm{ramification}\,\tau \cdot D_*(c)(D.\mathrm{pt}\,\tau)$; $\chi(\gamma) = \exp\bigl(2\pi i\,\mathrm{Re}(\mathrm{period}_N(\gamma)(f))\bigr)$, where $\mathrm{period}_N(\gamma)$ is the functional $g \mapsto \int_0^1 g(\text{segment from } i \text{ to } \gamma i)(\gamma i - i)\,dt$; and finally there exists $\Lambda$ in the period lattice, the $\mathbb{Z}$-span of the functionals $\mathrm{period}_N(\gamma)$ inside the $\mathbb{C}$-dual of $S_2(\Gamma_0(N))$, with $$\Bigl(\sum_\tau c(\tau)\,\mathrm{periodAlong}_N(i,\tau)\Bigr)(g) + i \int_{\mathcal{F}} \mathrm{petersson}_2(f,g)(\tau) = \Lambda(g)$$ for every weight-$2$ cusp form $g$, where $\mathcal{F}$ is the union over cosets $q \in \mathrm{SL}_2(\mathbb{Z})/\Gamma_0(N)$ of the translates $(\mathrm{Quotient.out}\,q)^{-1} \cdot \mathcal{D}$ of the standard fundamental domain.
--
--   This packages the classical construction of a differential of the third kind with prescribed residue divisor of degree zero on $X_0(N)_{\mathbb{C}}$, normalised so that its exponential primitive $F$ has unitary multipliers, together with the reciprocity law identifying the Abel–Jacobi image of the divisor, corrected by the Petersson pairing against a weight-$2$ cusp form, as a period lattice element. It is the form in which the construction is fed into [`ModularCurve.ComplexPlaceDictionary.multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLattice`](thm.html#ModularCurve.ComplexPlaceDictionary.multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLattice), on the way to the Abel–Jacobi description of divisor classes on the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ComplexPlaceDictionary_exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

theorem ModularCurve.ComplexPlaceDictionary.exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice
    {N : ℕ} [NeZero N] (D : ModularCurve.ComplexPlaceDictionary N) (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0) :
    ∃ (F : ℍ → ℂ) (χ : CongruenceSubgroup.Gamma0 N → ℂ)
      (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      (∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) ∧
      (∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 N, ‖χ γ‖ = 1) ∧
      (∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) ∧
      (∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
        (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ)) ∧
      (∀ γ : CongruenceSubgroup.Gamma0 N,
        χ γ = Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.period N γ f).re : ℂ))) ∧
      ∃ Λ ∈ ModularCurve.periodLattice N, ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
        (c.sum fun τ n => n • ModularCurve.periodAlong N UpperHalfPlane.I τ) g +
          Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
            (CongruenceSubgroup.Gamma0 N), UpperHalfPlane.petersson 2 f g τ) = Λ g := by sorry
