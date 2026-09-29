-- Prove2me | Theorems.Thm_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_isBaseChange
-- name    : HeckeEis.isEigensystemH1_of_isEigensystemH1_of_isBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/6c9badf8-a6a4-503a-b972-ac12b9c46b16
-- title:
--   Base change of an H¹ Hecke eigensystem along a field embedding
-- statement:
--   Fix $N \in \mathbb{N}$, fields $K_0$ and $K$, a ring homomorphism $i : K_0 \to K$, a set $S_0 \subseteq \mathbb{N}$, a $K_0$-vector space $V_0$ with a representation $\rho_0$ of $\Gamma_0(N)$, and a $K$-vector space $V$ with a representation $\rho$ of $\Gamma_0(N)$, together with families $a_0, a : \mathbb{N} \to \mathrm{End}(V_0), \mathrm{End}(V)$ of linear endomorphisms. Assume: (i) for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S_0$ and every $u$ in [`HeckeEis.heckeUpper N ℓ`](def/Gamma0HeckeOperatorHom.html#L128), the subgroup of elements of $\Gamma_0(N)$ whose upper-right entry is divisible by $\ell$, one has $a(\ell) \circ \rho(\mathrm{heckeConj}_{N,\ell}(u)) = \rho(u) \circ a(\ell)$, where $\mathrm{heckeConj}_{N,\ell}$ sends $g = \begin{pmatrix} g_{00} & g_{01} \\ g_{10} & g_{11}\end{pmatrix}$ to $\begin{pmatrix} g_{00} & g_{01}/\ell \\ \ell g_{10} & g_{11}\end{pmatrix}$; (ii) an $i$-semilinear map $j : V_0 \to V$ with $j(\rho_0(g)v) = \rho(g)(j v)$ for all $g \in \Gamma_0(N)$, $v \in V_0$, and $j(a_0(\ell)v) = a(\ell)(j v)$ for all primes $\ell \nmid N$ with $\ell \notin S_0$; (iii) $j$ is a base change, in the sense that there are an index type $\iota$, a $K_0$-basis $(b_0(s))_{s \in \iota}$ of $V_0$ and a $K$-basis $(b(s))_{s\in\iota}$ of $V$ with $b(s) = j(b_0(s))$ for all $s$. Let $\lambda : \mathbb{N} \to K_0$ and suppose [`HeckeEis.IsEigensystemH1 N ρ₀ a₀ S₀ lam`](def/Gamma0CoeffCohomologyEigen.html#L72) holds, i.e. there is a nonzero class $x$ in [`HeckeEis.coeffH1 ρ₀`](def/Gamma0CoeffCohomologyEigen.html#L16) (the quotient of the cocycles `coeffCocycles` by the coboundaries) such that for each prime $\ell \nmid N$, $\ell \notin S_0$ there is a $K_0$-linear endomorphism $T$ of `coeffH1 ρ₀` which is a Hecke operator on $H^1$ for $(\ell, a_0(\ell))$, meaning that every cocycle $z$ admits a cocycle $w$ whose underlying function is `coeffHeckeFun N ℓ ρ₀ (a₀ ℓ) z` with $T[z] = [w]$, and $Tx = \lambda(\ell)\, x$. Then the same holds over $K$: [`HeckeEis.IsEigensystemH1 N ρ a S₀ (fun ℓ => i (lam ℓ))`](def/Gamma0CoeffCohomologyEigen.html#L72).
--
--   This is the transport of a Hecke eigensystem in the group cohomology $H^1(\Gamma_0(N), V_0)$, in the cocycle-level formulation used throughout this development, along a semilinear base change $j : V_0 \to V$ over a homomorphism of coefficient fields; taking $i = \mathrm{id}$ it also covers transport along an equivariant isomorphism. It is used to pass eigensystems from a prime field to an arbitrary field of the same characteristic and from a $q$-expansion congruence statement to the cohomological one, in [`HeckeEis.isEigensystemH1_steinberg_quotient_of_isEigensystemH1_steinberg_quotient_of_charP`](thm.html#HeckeEis.isEigensystemH1_steinberg_quotient_of_isEigensystemH1_steinberg_quotient_of_charP) and [`HeckeEis.isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr`](thm.html#HeckeEis.isEigensystemH1_of_H1_gammaH_dual_of_isCuspidalOfType_of_qCoeff_congr).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_isBaseChange.lean

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HeckeEis.isEigensystemH1_of_isEigensystemH1_of_isBaseChange
    (N : ℕ) {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (S₀ : Set ℕ)
    {V₀ V : Type} [AddCommGroup V₀] [Module K₀ V₀] [AddCommGroup V] [Module K V]
    (ρ₀ : Representation K₀ (CongruenceSubgroup.Gamma0 N) V₀) (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V)
    (a₀ : ℕ → (V₀ →ₗ[K₀] V₀)) (a : ℕ → (V →ₗ[K] V))
    (ha : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
        a ℓ ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a ℓ)
    (j : V₀ →ₛₗ[i] V) (hj : ∀ (g : CongruenceSubgroup.Gamma0 N) (v : V₀), j (ρ₀ g v) = ρ g (j v))
    (hja : ∀ (ℓ : ℕ) (v : V₀), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → j (a₀ ℓ v) = a ℓ (j v))
    (hbc : ∃ (ι : Type) (b₀ : Module.Basis ι K₀ V₀) (b : Module.Basis ι K V), ∀ s : ι, b s = j (b₀ s))
    (lam : ℕ → K₀) (h : HeckeEis.IsEigensystemH1 N ρ₀ a₀ S₀ lam) :
    HeckeEis.IsEigensystemH1 N ρ a S₀ (fun ℓ => i (lam ℓ)) := by sorry
