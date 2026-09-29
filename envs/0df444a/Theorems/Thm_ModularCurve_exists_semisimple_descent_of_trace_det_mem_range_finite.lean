-- Prove2me | Theorems.Thm_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite
-- name    : ModularCurve.exists_semisimple_descent_of_trace_det_mem_range_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/bce96a98-78c0-5434-93ed-975a963e39e0
-- title:
--   Descent to a finite field of traces, with semisimple image
-- statement:
--   Let $K \subseteq L$ be fields with $L$ a $K$-algebra, and write $G = L \simeq_{\mathrm{alg}[K]} L$ for the group of $K$-algebra automorphisms of $L$. Let $M$ be a natural number and $p$ a prime, let $\Omega$ be an algebraically closed field, let $k$ be a finite field and $\iota \colon k \to \Omega$ a ring homomorphism, let $V$ be an $\Omega$-vector space and $\rho \colon G \to \mathrm{GL}_\Omega(V)$ a group homomorphism into the $\Omega$-linear automorphisms of $V$. Assume $p = 0$ in $\Omega$, $\dim_\Omega V = 2$, the image $\rho(G)$ is finite, every $G$-stable $\Omega$-subspace of $V$ is $\bot$ or $\top$, and for every $\sigma \in G$ both $\operatorname{tr} \rho(\sigma)$ and $\det \rho(\sigma)$ lie in the image of $\iota$. Assume further that $\rho$ has cyclotomic determinant at level $M$ in the sense of [`ModularCurve.CyclotomicDeterminant M p ρ`](def/ModularCurve_ResidualRealization.html#L44): for every prime $\ell \nmid Mp$, every valuation subring $A$ of $L$ with $\ell$ a nonunit of $A$, and every $\sigma \in G$ lying in the decomposition subgroup of $A$ over $K$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, one has $\det \rho(\sigma) = \ell$. Then there exist a $k$-vector space $V_0$ and a homomorphism $\rho_0 \colon G \to \mathrm{GL}_k(V_0)$ such that $\dim_k V_0 = 2$, $\rho_0$ satisfies [`ModularCurve.CyclotomicDeterminant M p ρ₀`](def/ModularCurve_ResidualRealization.html#L44), $\ker \rho \le \ker \rho_0$, $\iota(\operatorname{tr} \rho_0(\sigma)) = \operatorname{tr} \rho(\sigma)$ and $\iota(\det \rho_0(\sigma)) = \det \rho(\sigma)$ for all $\sigma \in G$, and every $G$-stable $k$-subspace of $V_0$ admits a $G$-stable complement.
--
--   This is the descent of a two-dimensional absolutely irreducible Galois representation with finite image, in characteristic $p$, from an algebraically closed coefficient field to a finite field containing its traces and determinants, the descended representation being recorded as semisimple (all $G$-stable subspaces complemented) rather than irreducible. It feeds the construction of the mod-$p$ residual representation attached to a Hecke eigenclass: it is used by [`ModularCurve.exists_matrixRep_trace_det_frobenius_of_heckeTorsion_ne_bot`](thm.html#ModularCurve.exists_matrixRep_trace_det_frobenius_of_heckeTorsion_ne_bot), [`GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range`](thm.html#GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range) and [`GaloisRep.exists_galoisFactorsThroughFiniteLevel_trace_eq_theta_heckeT_and_det_eq_pow`](thm.html#GaloisRep.exists_galoisFactorsThroughFiniteLevel_trace_eq_theta_heckeT_and_det_eq_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite.lean

import Mathlib
import Definitions.Def_ModularCurve_ResidualRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_semisimple_descent_of_trace_det_mem_range_finite
    {K L : Type} [Field K] [Field L] [Algebra K L] (M p : ℕ) [Fact p.Prime]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (k : Type) [Field k] [Finite k] (ι : k →+* Ω)
    (V : Type) [AddCommGroup V] [Module Ω V] (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[Ω] V))
    (hp : (p : Ω) = 0) (hV : Module.finrank Ω V = 2) (hfin : Finite ρ.range)
    (hirr : ∀ W : Submodule Ω V, (∀ σ, ∀ v ∈ W, ρ σ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ σ, LinearMap.trace Ω V (ρ σ).toLinearMap ∈ ι.range)
    (hdet : ∀ σ, LinearMap.det (ρ σ).toLinearMap ∈ ι.range)
    (hcyc : ModularCurve.CyclotomicDeterminant M p ρ) :
    ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module k V₀)
      (ρ₀ : (L ≃ₐ[K] L) →* (V₀ ≃ₗ[k] V₀)),
      Module.finrank k V₀ = 2 ∧
      ModularCurve.CyclotomicDeterminant M p ρ₀ ∧
      ρ.ker ≤ ρ₀.ker ∧
      (∀ σ, ι (LinearMap.trace k V₀ (ρ₀ σ).toLinearMap) = LinearMap.trace Ω V (ρ σ).toLinearMap) ∧
      (∀ σ, ι (LinearMap.det (ρ₀ σ).toLinearMap) = LinearMap.det (ρ σ).toLinearMap) ∧
      (∀ W : Submodule k V₀, (∀ σ, ∀ v ∈ W, ρ₀ σ v ∈ W) →
        ∃ W' : Submodule k V₀, (∀ σ, ∀ v ∈ W', ρ₀ σ v ∈ W') ∧ IsCompl W W') := by sorry
