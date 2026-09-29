-- Prove2me | Theorems.Thm_ModularCurve_exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp
-- name    : ModularCurve.exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/f9a1799d-889f-522c-8ac1-d71ffa637401
-- title:
--   Chain bounding div F with periods cancelling a Petersson integral
-- statement:
--   Let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index containing $-1$, let $F : \mathbb{H} \to \mathbb{C}$ be a function and let $k$ be a cusp form of weight $2$ for $\Gamma$. Assume: (hF) for every $\tau \in \mathbb{H}$ the function $z \mapsto F(\mathrm{ofComplex}\,z)$ is meromorphic at $\tau$; (hχ) for every $\gamma \in \Gamma$ and $\tau \in \mathbb{H}$ one has $F(\gamma \cdot \tau) = \exp\bigl(2\pi i \,\mathrm{Re}\,(\mathrm{periodOf}\,\Gamma\,\gamma)(k)\bigr)\, F(\tau)$, where $(\mathrm{periodOf}\,\Gamma\,\gamma)(f) = \int_0^1 f(\mathrm{segmentPath}\,i\,(\gamma\cdot i)\,t)\,(\gamma\cdot i - i)\,dt$ is integration of $f$ along the straight segment from $i$ to $\gamma \cdot i$; (hcusp) for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ the function $\tau \mapsto F(\sigma \cdot \tau)$ tends, along `atImInfty`, to some non-zero limit. Then there is a finitely supported $Z : \mathbb{H} \times \mathbb{H} \to \mathbb{Z}$ — a finite integral chain of oriented segments — such that, first, for every $\tau \in \mathbb{H}$ the meromorphic order of $z \mapsto F(\mathrm{ofComplex}\,z)$ at $\tau$ is an integer $n$ satisfying $$2n = \#\mathrm{Stab}_\Gamma(\tau) \cdot \sum_{(a,b)} Z(a,b)\bigl([b \in \Gamma\tau] - [a \in \Gamma\tau]\bigr),$$ i.e. the $\Gamma$-pushforward of the boundary of $Z$ is the divisor of $F$ with the indicated stabiliser weighting; and, second, for every cusp form $g$ of weight $2$ for $\Gamma$, $$\sum_{(a,b)} Z(a,b)\,(\mathrm{periodAlongOf}\,\Gamma\,a\,b)(g) + i \int_{\mathcal{F}_\Gamma} \mathrm{petersson}\,2\,k\,g = 0,$$ where $\mathcal{F}_\Gamma = \bigcup_{q \in \mathrm{SL}_2(\mathbb{Z})/\Gamma} q_{\mathrm{out}}^{-1} \cdot \mathcal{D}$ is the union of coset translates of the standard fundamental domain $\mathcal{D}$.
--
--   This is the chain form of twisted reciprocity on the modular curve $X(\Gamma)$: it produces simultaneously a segment chain whose boundary realises the divisor of a multiplicatively $\Gamma$-quasi-invariant function $F$ and the vanishing of its period functional plus $i$ times the weight-$2$ Petersson integral against the twisting cusp form $k$. It supplies the necessity half of the harmonic-twist Abel theorem and is cited by [`ModularCurve.periodAlongOf_add_petersson_mem_periodLatticeOf_of_multiplier_eq_exp`](thm.html#ModularCurve.periodAlongOf_add_petersson_mem_periodLatticeOf_of_multiplier_eq_exp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

set_option autoImplicit false
open Classical in

theorem ModularCurve.exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ Z : (ℍ × ℍ) →₀ ℤ,
      (∀ τ : ℍ, ∃ n : ℤ,
        meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
          2 * n = (Nat.card (MulAction.stabilizer (Γ) τ) : ℤ) *
            Z.sum (fun e m =>
              (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.2 = τ then m else 0) -
              (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.1 = τ then m else 0))) ∧
      ∀ g : CuspForm (Γ) 2,
        (Z.sum fun e m => m • ModularCurve.periodAlongOf Γ e.1 e.2) g +
          Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
            (Γ), UpperHalfPlane.petersson 2 k g τ) = 0 := by sorry
