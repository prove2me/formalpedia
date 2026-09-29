-- Prove2me | Theorems.Thm_IsNoetherianRing_exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring
-- name    : IsNoetherianRing.exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/cf9f105c-35dd-5e35-81f3-67faa107e840
-- title:
--   Globalising an n-th root of unity from geometric points
-- statement:
--   Let $R$ be a commutative Noetherian ring, living in a fixed universe, and let $n$ be a natural number whose image in $R$ is a unit. Suppose given a rule $c$ which to every algebraically closed field $\Omega$ (of the same universe) and every ring homomorphism $\varphi : R \to \Omega$ assigns an element $c_\Omega(\varphi) \in \Omega$, subject to two hypotheses. First, $c_\Omega(\varphi)^n = 1$ for all such $\Omega$ and $\varphi$. Second, a compatibility with valuation rings: for every algebraically closed field $K$, every valuation subring $\mathcal{O} \subseteq K$, every algebraically closed field $\Omega$, every ring homomorphism $\rho : R \to \mathcal{O}$ and every ring homomorphism $\psi : \mathcal{O} \to \Omega$, there exists $u \in \mathcal{O}$ with $c_K(\iota \circ \rho) = \iota(u)$, where $\iota : \mathcal{O} \to K$ is the inclusion, and $c_\Omega(\psi \circ \rho) = \psi(u)$. The conclusion is that there exists a single element $\varepsilon \in R$ with $\varepsilon^n = 1$ such that $c_\Omega(\varphi) = \varphi(\varepsilon)$ for every algebraically closed field $\Omega$ and every ring homomorphism $\varphi : R \to \Omega$.
--
--   This is an affine, elementary form of the statement that a section of the finite étale group scheme $\mu_n$ over a Noetherian base is determined by, and may be constructed from, a choice of one geometric point in each geometric fibre that is stable under specialisation and generalisation, the valuation-ring hypothesis encoding both compatibility with maps of algebraically closed fields (take $\mathcal{O} = K$) and with specialisation (take $\psi$ the residue map). It is used in the analysis of level components of modular curves, to produce a global root of unity out of Weil-pairing values computed at geometric points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsNoetherianRing_exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem IsNoetherianRing.exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ) (hn : IsUnit ((n : ℕ) : R))
    (c : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω], (R →+* Ω) → Ω)
    (hc : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω), c Ω φ ^ n = 1)
    (hv : ∀ (K : Type u) [Field K] [IsAlgClosed K] (𝒪 : ValuationSubring K)
      (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ρ : R →+* 𝒪) (ψ : 𝒪 →+* Ω),
      ∃ u : 𝒪, c K ((algebraMap 𝒪 K).comp ρ) = algebraMap 𝒪 K u ∧ c Ω (ψ.comp ρ) = ψ u) :
    ∃ ε : R, ε ^ n = 1 ∧ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω), c Ω φ = φ ε := by sorry
