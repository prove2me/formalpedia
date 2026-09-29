-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_modularFunctionFieldC_apply_jGeomGen_eq_comp
-- name    : ModularCurve.exists_algEquiv_modularFunctionFieldC_apply_jGeomGen_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/7eaad14e-d7c7-5190-b6f3-c51b2ad57729
-- title:
--   Rigidity of embeddings of modular function fields fixing j
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \nmid M$. Let $\kappa$ and $k$ be fields of characteristic $p$ with $k$ algebraically closed, and let $\tau : \kappa \to k$ be a ring homomorphism. For a field $K$, write $F_M(K) \subseteq \mathrm{LaurentSeries}(K)$ for the intermediate field $K(\tilde\jmath, \tilde\jmath_M)$ obtained by adjoining to $K$ the two Laurent series $\tilde\jmath = \mathtt{jqModC}\,K$ (the series $q^{-1}$ times the reduction to $K$ of the integral power series $\mathtt{jNum}$, i.e. the $q$-expansion of $j$) and $\tilde\jmath_M = \mathtt{jqNModC}\,K\,M$, its image under the substitution $q \mapsto q^M$; write $\mathtt{jGeomGen}\,K\,M$ for $\tilde\jmath$ regarded as an element of $F_M(K)$. Let $\theta, \theta_0 : F_M(\kappa) \to F_M(k)$ be ring homomorphisms such that each sends a constant $c \in \kappa$ to the constant $\tau(c)$, and each sends $\mathtt{jGeomGen}\,\kappa\,M$ to $\mathtt{jGeomGen}\,k\,M$. Then there is a $k$-algebra automorphism $\alpha$ of $F_M(k)$ with $\alpha(\mathtt{jGeomGen}\,k\,M) = \mathtt{jGeomGen}\,k\,M$ and $\theta(f) = \alpha(\theta_0(f))$ for every $f \in F_M(\kappa)$.
--
--   This is a rigidity statement for the level-$M$ modular function field in characteristic $p$: any two ring homomorphisms $F_M(\kappa) \to F_M(k)$ inducing the same map $\tau$ on constants and both fixing the $q$-expansion of $j$ differ only by a $k$-automorphism of $F_M(k)$ over $k(j)$, so that such a homomorphism is canonical up to the Galois action of the modular equation $\Phi_M(\tilde\jmath, Y)$. It is used in the computation of the cardinality of inertia on the special fibre of $X_0(pM)$, where an abstractly given attachment map must be compared with the canonical coefficient-change map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_modularFunctionFieldC_apply_jGeomGen_eq_comp.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularEquationQ

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_algEquiv_modularFunctionFieldC_apply_jGeomGen_eq_comp
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (κ k : Type) [Field κ] [CharP κ p] [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k]
    (τ : κ →+* k)
    (θ θ₀ : ↥(ModularCurve.modularFunctionFieldC κ M) →+* ↥(ModularCurve.modularFunctionFieldC k M))
    (hθκ : ∀ c : κ, θ (algebraMap κ _ c) = algebraMap k _ (τ c))
    (hθ₀κ : ∀ c : κ, θ₀ (algebraMap κ _ c) = algebraMap k _ (τ c))
    (hθj : θ (ModularCurve.jGeomGen κ M) = ModularCurve.jGeomGen k M)
    (hθ₀j : θ₀ (ModularCurve.jGeomGen κ M) = ModularCurve.jGeomGen k M) :
    ∃ α : ↥(ModularCurve.modularFunctionFieldC k M) ≃ₐ[k] ↥(ModularCurve.modularFunctionFieldC k M),
      α (ModularCurve.jGeomGen k M) = ModularCurve.jGeomGen k M ∧ ∀ f, θ f = α (θ₀ f) := by sorry
