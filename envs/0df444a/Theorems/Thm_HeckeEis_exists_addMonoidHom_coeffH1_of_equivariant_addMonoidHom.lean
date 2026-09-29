-- Prove2me | Theorems.Thm_HeckeEis_exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom
-- name    : HeckeEis.exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/dcd1e9b0-1267-533d-8ec5-3e2845ba9497
-- title:
--   Semilinear change of coefficients on Γ₀(N)-coefficient cohomology
-- statement:
--   Let $N$ be a natural number, let $R$ and $\kappa$ be commutative rings and $f \colon R \to \kappa$ a ring homomorphism, let $\Lambda$ be an $R$-module and $\Lambda'$ a $\kappa$-module, and let $\rho_R$ and $\rho'$ be representations of $\Gamma_0(N)$ on $\Lambda$ and on $\Lambda'$ over $R$ and $\kappa$ respectively. Suppose given an additive map $\mathrm{red} \colon \Lambda \to \Lambda'$ with $\mathrm{red}(c \cdot x) = f(c) \cdot \mathrm{red}(x)$ for all $c \in R$, $x \in \Lambda$, and $\mathrm{red}(\rho_R(g)x) = \rho'(g)\,\mathrm{red}(x)$ for all $g \in \Gamma_0(N)$, together with families of endomorphisms $a_\ell$ of $\Lambda$ ($R$-linear) and $a'_\ell$ of $\Lambda'$ ($\kappa$-linear), indexed by $\ell \in \mathbb{N}$, satisfying $\mathrm{red} \circ a_\ell = a'_\ell \circ \mathrm{red}$. Here [`HeckeEis.coeffCocycles`](def/Gamma0CoeffCohomology.html#L13) is the module of functions $z \colon \Gamma_0(N) \to \Lambda$ with $z(gh) = z(g) + \rho_R(g)z(h)$, [`HeckeEis.coeffH1`](def/Gamma0CoeffCohomologyEigen.html#L16) its quotient by the cocycles lying in the coboundaries, and [`HeckeEis.coeffH1Mk`](def/Gamma0CoeffCohomologyEigen.html#L27) the class map. The assertion is the existence of an additive map $\Phi \colon \mathrm{coeffH1}(\rho_R) \to \mathrm{coeffH1}(\rho')$ with four properties: (i) for every cocycle $z$ there is a cocycle $w$ with $w(g) = \mathrm{red}(z(g))$ for all $g$ and $\Phi[z] = [w]$; (ii) $\Phi(c \cdot x) = f(c) \cdot \Phi(x)$ for all $c \in R$; (iii) for every nonzero $\ell$ and every pair of linear operators $T$ on $\mathrm{coeffH1}(\rho_R)$ and $T'$ on $\mathrm{coeffH1}(\rho')$ satisfying [`HeckeEis.IsCoeffHeckeOnH1`](def/Gamma0CoeffCohomologyEigen.html#L61) at level $N$, index $\ell$ with coefficient parts $a_\ell$ and $a'_\ell$ — that is, each sends the class of a cocycle to the class of the cocycle given by the explicit coset sum [`HeckeEis.coeffHeckeFun`](def/Gamma0CoeffCohomology.html#L129) — one has $\Phi \circ T = T' \circ \Phi$; and (iv) for every $\varpi \in R$ such that $\mathrm{red}$ is surjective, $\mathrm{red}(x) = 0$ holds exactly when $x \in \varpi\Lambda$, and multiplication by $\varpi$ on $\Lambda$ is injective, the kernel of $\Phi$ is precisely $\varpi \cdot \mathrm{coeffH1}(\rho_R)$.
--
--   This is the change-of-coefficients map on the group cohomology $H^1(\Gamma_0(N), -)$ used in the cohomological theory of Hecke operators: reduction of coefficients along $f$ induces a semilinear map on $H^1$ commuting with the Hecke operators at all $\ell$, and, in the case of reduction modulo a regular element $\varpi$ acting with kernel exactly $\varpi\Lambda$, with kernel exactly the $\varpi$-multiples. It is invoked to transport Hecke eigensystems on $H^1$ to the residue field of a discrete valuation ring and to a Steinberg quotient in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom.lean

import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup

theorem HeckeEis.exists_addMonoidHom_coeffH1_of_equivariant_addMonoidHom
    (N : ℕ) {R : Type} [CommRing R] {κ : Type} [CommRing κ] (f : R →+* κ)
    {Λ : Type} [AddCommGroup Λ] [Module R Λ] {Λ' : Type} [AddCommGroup Λ'] [Module κ Λ']
    (ρR : Representation R (Gamma0 N) Λ) (ρ' : Representation κ (Gamma0 N) Λ')
    (red : Λ →+ Λ') (hreds : ∀ (c : R) (x : Λ), red (c • x) = f c • red x)
    (hredρ : ∀ (g : Gamma0 N) (x : Λ), red (ρR g x) = ρ' g (red x))
    (a : ℕ → (Λ →ₗ[R] Λ)) (a' : ℕ → (Λ' →ₗ[κ] Λ')) (hreda : ∀ (ℓ : ℕ) (x : Λ), red (a ℓ x) = a' ℓ (red x)) :
    ∃ Φ : HeckeEis.coeffH1 ρR →+ HeckeEis.coeffH1 ρ',
      (∀ z : ↥(HeckeEis.coeffCocycles ρR), ∃ w : ↥(HeckeEis.coeffCocycles ρ'),
        (∀ g : Gamma0 N, (w : Gamma0 N → Λ') g = red ((z : Gamma0 N → Λ) g)) ∧
          Φ (HeckeEis.coeffH1Mk ρR z) = HeckeEis.coeffH1Mk ρ' w) ∧
      (∀ (c : R) (x : HeckeEis.coeffH1 ρR), Φ (c • x) = f c • Φ x) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ] (T : HeckeEis.coeffH1 ρR →ₗ[R] HeckeEis.coeffH1 ρR)
          (T' : HeckeEis.coeffH1 ρ' →ₗ[κ] HeckeEis.coeffH1 ρ'),
        HeckeEis.IsCoeffHeckeOnH1 N ℓ ρR (a ℓ) T → HeckeEis.IsCoeffHeckeOnH1 N ℓ ρ' (a' ℓ) T' →
          ∀ x : HeckeEis.coeffH1 ρR, Φ (T x) = T' (Φ x)) ∧
      ∀ ϖ : R, Function.Surjective red → (∀ x : Λ, red x = 0 ↔ ∃ y : Λ, x = ϖ • y) → (∀ x : Λ, ϖ • x = 0 → x = 0) →
        ∀ x : HeckeEis.coeffH1 ρR, Φ x = 0 ↔ ∃ y : HeckeEis.coeffH1 ρR, x = ϖ • y := by sorry
