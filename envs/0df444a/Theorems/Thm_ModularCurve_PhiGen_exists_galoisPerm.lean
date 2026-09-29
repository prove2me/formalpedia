-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_exists_galoisPerm
-- name    : ModularCurve.PhiGen.exists_galoisPerm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/372db64a-d7eb-5ae5-8db4-6cf5bef16d73
-- title:
--   A field endomorphism permutes the ℓ-th roots of unity
-- statement:
--   Let $K$ be a field, let $\ell$ be a natural number which is prime (recorded as a `Fact` instance), and let $\zeta$ be a unit of $K$ whose underlying element is a primitive $\ell$-th root of unity in $K$. Let $\sigma \colon K \to K$ be any ring homomorphism from $K$ to itself (not assumed bijective, nor continuous, nor the identity on any subfield). The assertion is that there exists a permutation $e$ of the finite index type `Fin ℓ`, that is a bijection $e \colon \mathrm{Fin}\,\ell \simeq \mathrm{Fin}\,\ell$, such that for every $b \in \mathrm{Fin}\,\ell$ one has $\sigma(\zeta^{b}) = \zeta^{e(b)}$, the exponents on both sides being the natural numbers underlying $b$ and $e(b)$ under the coercion $\mathrm{Fin}\,\ell \to \mathbb{N}$. Thus the group $\mu_\ell \subset K^\times$ of $\ell$-th roots of unity, enumerated as $\zeta^{0}, \zeta^{1}, \dots, \zeta^{\ell-1}$, is carried to itself bijectively by $\sigma$, with the permutation of the exponent set $\mathrm{Fin}\,\ell$ produced explicitly; note that $b = 0$ is included, so $e$ necessarily fixes $0$.
--
--   This is the elementary statement that a field endomorphism acts on the $\ell$-th roots of unity of $K$ through a permutation of their exponents modulo $\ell$, here packaged as a bijection of `Fin ℓ` so that sums and products indexed by exponents may be reindexed. It is used in the study of $q$-expansions at level $\ell$ and their Galois conjugates, being cited in the results on Fricke involutions, integrality over $\mathbb{Z}[j(q)]$ and membership in the modular function field for $\Gamma_0$-invariant expansions, alongside the compatibility of [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) with [`ModularCurve.qExpand`](def/ModularCurve_X0.html#L25).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_exists_galoisPerm.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.exists_galoisPerm {K : Type*} [Field K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) (σ : K →+* K) : ∃ e : Fin ℓ ≃ Fin ℓ, ∀ b : Fin ℓ, σ ((ζ : K) ^ (b : ℕ)) = (ζ : K) ^ ((e b : Fin ℓ) : ℕ) := by sorry
