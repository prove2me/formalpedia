-- Prove2me | Theorems.Thm_ModularCurve_exists_realize_eventuallyEq_of_meromorphic
-- name    : ModularCurve.exists_realize_eventuallyEq_of_meromorphic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/54e224ed-73f5-50db-a243-d65c3594e2f8
-- title:
--   Analytic functions on X₀(N) are realizations of ℂF_N
-- statement:
--   Let $N$ be a positive integer and let $F \colon \mathbb{H} \to \mathbb{C}$ be a function on the upper half-plane subject to three hypotheses: (i) for every $\tau \in \mathbb{H}$ the function $z \mapsto F(\mathrm{ofComplex}\, z)$ of a complex variable is meromorphic at the point $\tau \in \mathbb{C}$, where `ofComplex` is the retraction of $\mathbb{C}$ onto $\mathbb{H}$; (ii) $F(\gamma \cdot \tau) = F(\tau)$ for all $\gamma \in \Gamma_0(N)$ and all $\tau \in \mathbb{H}$; (iii) for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ there is a real $C$ with $\tau \mapsto F(\sigma \cdot \tau)$ of order $O(\exp(C \operatorname{Im} \tau))$ along the filter $\operatorname{atImInfty}$. The conclusion asserts the existence of a Laurent series $x$ lying in [`ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)`](def/ModularCurve_LaurentCoeff.html#L103) — that is, in the subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise images of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the series $\mathrm{qExpand}_{\mathbb{Q}}\, d\, jq$ for the nonzero divisors $d \mid N$ — such that for every $\tau \in \mathbb{H}$ the functions $z \mapsto F(\mathrm{ofComplex}\, z)$ and $z \mapsto \mathrm{realize}\, N\, x\, (\mathrm{ofComplex}\, z)$ agree on a punctured neighbourhood of $\tau$ in $\mathbb{C}$. Here $\mathrm{realize}\, N\, x\, (\tau)$ is, by definition, $g(\tau)/h(\tau)$ for a chosen pair $g, h$ of modular forms of some common weight $k$ on $\Gamma_0(N)$ with $h(\tau) \neq 0$ and $x \cdot \widetilde{h} = \widetilde{g}$ in $\mathbb{C}((q))$ ($\widetilde{f}$ denoting the $q$-expansion of $f$ of width $1$), and $0$ if no such pair exists.
--
--   This is the comparison between the analytic and the algebraic function field of $X_0(N)$: a $\Gamma_0(N)$-invariant function on $\mathbb{H}$ that is meromorphic on $\mathbb{H}$ and of at most exponential growth at every cusp is, locally everywhere, the realization of an element of $\mathbb{C}(j(q^d) : d \mid N)$. It is used in the proof that an analytically constructed meromorphic function on $X_0(N)$ has an algebraic principal divisor, via [`ModularCurve.ComplexPlaceDictionary.isPrincipal_of_abelJacobi_mem_periodLattice`](thm.html#ModularCurve.ComplexPlaceDictionary.isPrincipal_of_abelJacobi_mem_periodLattice). Uniqueness of $x$ is not part of the assertion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_realize_eventuallyEq_of_meromorphic.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_realize_eventuallyEq_of_meromorphic (N : ℕ) [NeZero N]
    (F : ℍ → ℂ)
    (hmer : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ C : ℝ,
      Asymptotics.IsBigO atImInfty (fun τ : ℍ => F (σ • τ)) fun τ : ℍ => Real.exp (C * τ.im)) :
    ∃ x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N),
      ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => ModularCurve.realize N x (ofComplex z) := by sorry
