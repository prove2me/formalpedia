-- Prove2me | Theorems.Thm_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective
-- name    : HeckeEis.isEigensystemH1_of_isEigensystemH1_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/7d545225-6658-5221-8df6-391d1ad976ef
-- title:
--   Lifting Hecke eigensystems in H¹(Γ₀(N),·) along surjections
-- statement:
--   Fix an integer $N \ge 1$ and a field $\kappa$ with $6 \ne 0$ in $\kappa$, and a set $S_0 \subseteq \mathbb{N}$. Let $V$ be a finite-dimensional $\kappa$-vector space carrying a representation $\rho$ of $\Gamma_0(N) \subseteq \mathrm{SL}_2(\mathbb{Z})$, let $V''$ be a $\kappa$-module carrying a representation $\rho''$ of $\Gamma_0(N)$, and let $a, a'' \colon \mathbb{N} \to \mathrm{End}_\kappa(V), \mathrm{End}_\kappa(V'')$ be families of coefficient maps. Assume: (i) for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S_0$ and every $u$ in [`HeckeEis.heckeUpper N ℓ`](def/Gamma0HeckeOperatorHom.html#L128), the subgroup of $\gamma \in \Gamma_0(N)$ with $\ell$ dividing the upper right entry, one has $a_\ell \circ \rho(\mathrm{hc}(u)) = \rho(u) \circ a_\ell$, where $\mathrm{hc} =$ [`HeckeEis.heckeConj N ℓ`](def/Gamma0HeckeOperatorHom.html#L172) sends $\begin{pmatrix} x & y \\ z & w\end{pmatrix}$ to $\begin{pmatrix} x & y/\ell \\ z\ell & w\end{pmatrix}$; (ii) $a_\ell$ and $a_{\ell'}$ commute for all such primes $\ell, \ell'$; (iii) there is a surjective $\kappa$-linear $\pi \colon V \to V''$ with $\pi \circ \rho(g) = \rho''(g) \circ \pi$ for all $g \in \Gamma_0(N)$ and $\pi \circ a_\ell = a''_\ell \circ \pi$ for all such primes $\ell$. Let $\lambda \colon \mathbb{N} \to \kappa$ and suppose [`HeckeEis.IsEigensystemH1 N ρ'' a'' S₀ lam`](def/Gamma0CoeffCohomologyEigen.html#L72) holds. Then [`HeckeEis.IsEigensystemH1 N ρ a S₀ lam`](def/Gamma0CoeffCohomologyEigen.html#L72) holds, that is: there is a nonzero class $x$ in [`HeckeEis.coeffH1 ρ`](def/Gamma0CoeffCohomologyEigen.html#L16), the quotient of the inhomogeneous $1$-cocycles on $\Gamma_0(N)$ with values in $V$ by the coboundaries, such that for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S_0$ there is a $\kappa$-linear endomorphism $T$ of [`HeckeEis.coeffH1 ρ`](def/Gamma0CoeffCohomologyEigen.html#L16) which is induced by the cochain-level operator [`HeckeEis.coeffHeckeFun N ℓ ρ (a ℓ)`](def/Gamma0CoeffCohomology.html#L129) — for every cocycle $z$ there is a cocycle $w$ whose underlying function equals `coeffHeckeFun N ℓ ρ (a ℓ) z` and with $T[z] = [w]$ — and $T x = \lambda(\ell)\, x$.
--
--   This is the lifting half of the standard eigenclass-transfer argument for Hecke eigensystems in the first cohomology of $\Gamma_0(N)$: an eigensystem occurring in a quotient coefficient module is realised in the module itself, the passage relying on the vanishing of $H^2(\Gamma_0(N), \cdot)$ when $6$ is invertible. It is used in the reduction of eigensystems to level one and in the dichotomy between eigensystems coming from the Steinberg quotient and Eisenstein ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_surjective.lean

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.isEigensystemH1_of_isEigensystemH1_of_surjective
    (N : ℕ) [NeZero N] {κ : Type} [Field κ] (h6 : (6 : κ) ≠ 0) (S₀ : Set ℕ)
    {V V'' : Type} [AddCommGroup V] [Module κ V] [FiniteDimensional κ V] [AddCommGroup V''] [Module κ V'']
    (ρ : Representation κ (CongruenceSubgroup.Gamma0 N) V) (ρ'' : Representation κ (CongruenceSubgroup.Gamma0 N) V'')
    (a : ℕ → (V →ₗ[κ] V)) (a'' : ℕ → (V'' →ₗ[κ] V''))
    (ha : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
        a ℓ ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a ℓ)
    (hcomm : ∀ ℓ ℓ' : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → ℓ'.Prime → ¬ ℓ' ∣ N → ℓ' ∉ S₀ →
      a ℓ ∘ₗ a ℓ' = a ℓ' ∘ₗ a ℓ)
    (π : V →ₗ[κ] V'') (hπ : ∀ g : CongruenceSubgroup.Gamma0 N, π ∘ₗ ρ g = ρ'' g ∘ₗ π)
    (hπa : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → π ∘ₗ a ℓ = a'' ℓ ∘ₗ π)
    (hsurj : Function.Surjective π)
    (lam : ℕ → κ) (h : HeckeEis.IsEigensystemH1 N ρ'' a'' S₀ lam) :
    HeckeEis.IsEigensystemH1 N ρ a S₀ lam := by sorry
