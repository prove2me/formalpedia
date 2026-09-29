-- Prove2me | Theorems.Thm_ModularCurve_exists_realizeOf_eventuallyEq_of_meromorphic_gammaH
-- name    : ModularCurve.exists_realizeOf_eventuallyEq_of_meromorphic_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/d2abf351-01d7-5970-bd8b-718037087d5a
-- title:
--   GAGA for X_H(M): invariant meromorphic functions are algebraic
-- statement:
--   Fix a natural number $M \neq 0$ and a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^{\times}$ given by the lower right entry modulo $M$. Let $F : \mathfrak{H} \to \mathbb{C}$ be a function on the upper half plane such that: for every $\tau \in \mathfrak{H}$ the function $z \mapsto F(\mathrm{ofComplex}\, z)$ on $\mathbb{C}$ (where `UpperHalfPlane.ofComplex` is the retraction of $\mathbb{C}$ onto $\mathfrak{H}$) is meromorphic at the point $\tau$; $F(\gamma \cdot \tau) = F(\tau)$ for all $\gamma \in \Gamma_H(M)$ and all $\tau$; and for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ there is a real constant $C$ with $F(\sigma \cdot \tau) = O(e^{C \operatorname{Im} \tau})$ along the filter $\operatorname{Im} \tau \to \infty$. Then there exists a Laurent series $x$ over $\mathbb{C}$ lying in [`ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)`](def/ModularCurve_LaurentCoeff.html#L103), the subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise image of the $q$-expansion function field [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79) $\subseteq \mathbb{Q}((q))$ attached to $\Gamma_H(M)$, such that for every $\tau \in \mathfrak{H}$ the functions $z \mapsto F(\mathrm{ofComplex}\, z)$ and $z \mapsto \mathrm{realizeOf}\,\Gamma_H(M)\, x\, (\mathrm{ofComplex}\, z)$ agree on a punctured neighbourhood of $\tau$ in $\mathbb{C}$. Here $\mathrm{realizeOf}\,\Gamma\, x\, \tau$ is $g(\tau)/h(\tau)$ for a chosen weight $k$ and pair of modular forms $g, h$ of weight $k$ on $\Gamma$ with $h(\tau) \neq 0$ and $x \cdot q\text{-}\mathrm{exp}(h) = q\text{-}\mathrm{exp}(g)$ in $\mathbb{C}((q))$ (period $1$ expansions), and $0$ if no such data exist.
--
--   This is the GAGA statement for the modular curve $X_H(M)$: a meromorphic $\Gamma_H(M)$-invariant function of at most exponential growth at the cusps is the realization of an element of the function field of $X_H(M)$, base changed to $\mathbb{C}$. It is used in the construction of the complex-place dictionary for $X_H(M)$, in particular by [`ModularCurve.ComplexPlaceDictionaryOf.isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH`](thm.html#ModularCurve.ComplexPlaceDictionaryOf.isPrincipal_of_abelJacobi_mem_periodLatticeOf_gammaH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_realizeOf_eventuallyEq_of_meromorphic_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology

theorem ModularCurve.exists_realizeOf_eventuallyEq_of_meromorphic_gammaH (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (F : UpperHalfPlane → ℂ)
    (hmer : ∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ))
    (hinv : ∀ γ ∈ CohCarrier.GammaH M H, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ C : ℝ,
      Asymptotics.IsBigO UpperHalfPlane.atImInfty (fun τ : UpperHalfPlane => F (σ • τ))
        fun τ : UpperHalfPlane => Real.exp (C * τ.im)) :
    ∃ x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H),
      ∀ τ : UpperHalfPlane, (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => ModularCurve.realizeOf (CohCarrier.GammaH M H) x (UpperHalfPlane.ofComplex z) := by sorry
