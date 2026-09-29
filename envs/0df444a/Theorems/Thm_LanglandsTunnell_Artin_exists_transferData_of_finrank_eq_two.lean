-- Prove2me | Theorems.Thm_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two
-- name    : LanglandsTunnell.Artin.exists_transferData_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/ecb291bd-fc8e-5896-9ef9-0000c3ef512a
-- title:
--   Artin transfer data for a quadratic extension at an admissible modulus
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a Galois extension of $K$ whose Galois group $L \simeq_{\mathrm{alg}[K]} L$ is commutative, and suppose $[L:K]=2$. Let $\mathfrak f$ be an ideal of $\mathcal O_K$ satisfying `IsAdmissibleModulus K L 𝔣`: $\mathfrak f \neq 0$, and for every height-one prime $v$ of $\mathcal O_K$ whose chosen prime `primeAbove K L v` has nontrivial inertia subgroup in $\mathrm{Gal}(L/K)$, the power $v^{4e(v\mid 2)+2e(v\mid 3)+1}$ divides $\mathfrak f$, where $e(v\mid \ell)$ is the ramification index of $(\ell)$ at $v$. Write $I_K(\mathfrak f)$ for `coprimeToModulus K 𝔣`, the subgroup of invertible fractional ideals of $K$ with vanishing valuation at every prime dividing $\mathfrak f$, and `primeCarriers K 𝔣` for the set of elements of $I_K(\mathfrak f)$ of the form `primeCarrier K 𝔣 v hv` with $v$ a height-one prime not dividing $\mathfrak f$. Then there exist an element $\sigma \in \mathrm{Gal}(L/K)$, a type $I$ carrying a commutative group structure, and families indexed by all of $I_K(\mathfrak f)$: group homomorphisms $N_{\mathfrak p} : I \to I_K(\mathfrak f)$ and $\omega_{\mathfrak p} : I \to \mathrm{Gal}(L/K)$, elements $P_{\mathfrak p} \in I$ and integers $d_{\mathfrak p}$, such that for all $\mathfrak p, \mathfrak q \in$ `primeCarriers K 𝔣` and all $x \in I$: the Artin symbol `artinSymbol K L 𝔣` (the homomorphism on $I_K(\mathfrak f)$ induced by $v \mapsto$ the arithmetic Frobenius at `primeAbove K L v`) of $N_{\mathfrak p}(x)$ equals $\omega_{\mathfrak p}(x)$; if $\omega_{\mathfrak p}(x)=1$ then $N_{\mathfrak p}(x)$ lies in `normRaySubgroup K L 𝔣`, the join inside $I_K(\mathfrak f)$ of the narrow ray subgroup and the image of the relative norm `relNormCTM K L 𝔣` from ideals of $L$ coprime to $\mathfrak f \mathcal O_L$; $N_{\mathfrak p}(P_{\mathfrak p}) = \mathfrak p$; $\omega_{\mathfrak p}(P_{\mathfrak p}) = \sigma^{d_{\mathfrak p}}$; and there are $b_{\mathfrak p}, b_{\mathfrak q} \in I$ with $N_{\mathfrak p}(b_{\mathfrak p}) = N_{\mathfrak q}(b_{\mathfrak q})$ and $\omega_{\mathfrak p}(b_{\mathfrak p}) = \sigma$. No condition asserting that $\sigma$ is the nontrivial element of $\mathrm{Gal}(L/K)$ is imposed, and the four families are required to satisfy the listed conditions only at the prime carriers.
--
--   These are the auxiliary data of Artin's proof of the reciprocity law by crossing with cyclotomic extensions, specialised to a quadratic extension and packaged as a single existence statement: each prime $\mathfrak p$ coprime to the modulus is equipped with a group of ideals mapping to $I_K(\mathfrak f)$ and to $\mathrm{Gal}(L/K)$ compatibly with the Artin symbol, a distinguished lift of $\mathfrak p$, and links between any two primes. It supports the comparison of Hecke eigensystems under formal base change used in the Langlands–Tunnell input to modularity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Artin_exists_transferData_of_finrank_eq_two.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField Deep.NTSupply
open LanglandsTunnell.P2.Artin

universe u v

theorem LanglandsTunnell.Artin.exists_transferData_of_finrank_eq_two
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)]
    (h2 : Module.finrank K L = 2) (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣) :
    ∃ (σ : L ≃ₐ[K] L) (Ip : Type (max u v)) (_ : CommGroup Ip)
      (N : ↥(coprimeToModulus K 𝔣) → (Ip →* ↥(coprimeToModulus K 𝔣)))
      (ωp : ↥(coprimeToModulus K 𝔣) → (Ip →* (L ≃ₐ[K] L)))
      (P : ↥(coprimeToModulus K 𝔣) → Ip) (d : ↥(coprimeToModulus K 𝔣) → ℤ),
      (∀ p ∈ primeCarriers K 𝔣, ∀ x, artinSymbol K L 𝔣 (N p x) = ωp p x) ∧
      (∀ p ∈ primeCarriers K 𝔣, ∀ x, ωp p x = 1 → N p x ∈ normRaySubgroup K L 𝔣) ∧
      (∀ p ∈ primeCarriers K 𝔣, N p (P p) = p) ∧
      (∀ p ∈ primeCarriers K 𝔣, ωp p (P p) = σ ^ d p) ∧
      (∀ p ∈ primeCarriers K 𝔣, ∀ q ∈ primeCarriers K 𝔣,
        ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ) := by sorry
