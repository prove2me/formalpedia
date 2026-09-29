-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_eventuallyEq_div_of_meromorphic
-- name    : ModularCurve.exists_modularForm_eventuallyEq_div_of_meromorphic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/c5ed6b65-0b44-5bf6-80a7-8320723a514a
-- title:
--   Meromorphic Γ₀(N)-invariant functions are quotients of modular forms
-- statement:
--   Let $N$ be a positive natural number and let $F : \mathbb{H} \to \mathbb{C}$ be a function on the upper half-plane, subject to three hypotheses. First, meromorphy on $\mathbb{H}$: transporting $F$ to the complex plane by the Mathlib section `ofComplex : ℂ → ℍ`, the function $z \mapsto F(\mathrm{ofComplex}\,z)$ is meromorphic at the point $\tau \in \mathbb{C}$ for every $\tau \in \mathbb{H}$. Second, invariance: $F(\gamma \cdot \tau) = F(\tau)$ for every $\gamma$ in the congruence subgroup $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$ and every $\tau \in \mathbb{H}$. Third, growth of exponential type at every cusp: for each $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ there is a real constant $C$ with $\tau \mapsto F(\sigma \cdot \tau)$ of order $O(\exp(C \cdot \operatorname{Im} \tau))$ along the filter `atImInfty`. The conclusion asserts the existence of an integer weight $k$ and of two modular forms $g, h$ of weight $k$ for $\Gamma_0(N)$, with $h \neq 0$, such that for every $\tau \in \mathbb{H}$ the functions $z \mapsto F(\mathrm{ofComplex}\,z)$ and $z \mapsto g(\mathrm{ofComplex}\,z)/h(\mathrm{ofComplex}\,z)$ agree on a punctured neighbourhood of $\tau$ in $\mathbb{C}$, i.e. eventually with respect to the filter $\mathcal{N}[\neq]\,\tau$.
--
--   This is the analytic input identifying meromorphic functions on the modular curve $X_0(N)$ with quotients $g/h$ of holomorphic modular forms of equal weight on $\Gamma_0(N)$, the growth condition at the cusps replacing meromorphy of the extension to the compactified curve. It is used by [`ModularCurve.exists_realize_eventuallyEq_of_meromorphic`](thm.html#ModularCurve.exists_realize_eventuallyEq_of_meromorphic) in the passage between the analytic and the algebraic models of $X_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_eventuallyEq_div_of_meromorphic.lean

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Meromorphic.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_modularForm_eventuallyEq_div_of_meromorphic (N : ℕ) [NeZero N]
    (F : ℍ → ℂ)
    (hmer : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ C : ℝ,
      Asymptotics.IsBigO atImInfty (fun τ : ℍ => F (σ • τ)) fun τ : ℍ => Real.exp (C * τ.im)) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => (g : ℍ → ℂ) (ofComplex z) / (h : ℍ → ℂ) (ofComplex z) := by sorry
