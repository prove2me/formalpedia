-- Prove2me | Theorems.Thm_ModularCurve_exists_isEigenformIdeal_of_isResiduallyModularOfLevel
-- name    : ModularCurve.exists_isEigenformIdeal_of_isResiduallyModularOfLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/c72e6b7c-2364-58e1-833d-c541ebd5100a
-- title:
--   Residual modularity of level N yields an eigenform ideal
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $p$ be a prime and let $N$ be a positive natural number, and assume `W.IsResiduallyModularOfLevel p N`: there are a weight-$2$ cusp form $f$ on $\Gamma_0(N)$ whose $q$-expansion coefficients satisfy the normalised-eigenform relations (first coefficient $1$, multiplicativity at coprime indices, and the two prime-power recursions according as the prime divides $N$ or not) and a maximal ideal $\mathfrak{M}$ of the integral closure $\overline{\mathbb{Z}}$ of $\mathbb{Z}$ in $\mathbb{C}$ with $p \in \mathfrak{M}$, such that for every prime $\ell$ with $\ell \nmid \Delta(W)$, $\ell \nmid N$ and $\ell \neq p$ the coefficient `qCoeff f ℓ` is the image in $\mathbb{C}$ of some $a \in \overline{\mathbb{Z}}$ with $a - a_\ell(W) \in \mathfrak{M}$, where $a_\ell(W) = \ell + 1 - \#W(\mathbb{F}_\ell)$ is computed from the reduction of $W$ modulo $\ell$. Then there is an ideal $\mathfrak{m}$ of [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14) $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$ such that: $\mathfrak{m}$ is an eigenform ideal of level $N$, i.e. there are a normalised eigenform $g$ of weight $2$ on $\Gamma_0(N)$, a finite field $k$, a subring $\mathcal{O} \subseteq \mathbb{C}$ containing `qCoeff g ℓ` for every prime $\ell$, and a ring homomorphism $\varphi : \mathcal{O} \to k$, with $\mathfrak{m}$ the kernel of the $\mathbb{Z}$-algebra map sending $X_\ell \mapsto \varphi(\mathrm{qCoeff}\,g\,\ell)$; moreover the constant $p$ lies in $\mathfrak{m}$, and $X_\ell - a_\ell(W) \in \mathfrak{m}$ for every prime $\ell$ with $\ell \nmid \Delta(W)$, $\ell \nmid N$ and $\ell \neq p$.
--
--   This is the passage from residual modularity stated in terms of Fourier coefficients and a maximal ideal of the algebraic integers to the purely algebraic formulation used throughout the project, in which a mod-$p$ system of Hecke eigenvalues is recorded as an ideal of the free polynomial Hecke algebra $\mathbb{Z}[X_\ell]$; integrality of the eigenvalues comes from finite generation of the Hecke algebra acting on cusp forms and from the identification of the operators $T_\ell$ and $U_q$ with multiplication by $q$-expansion coefficients on an eigenform. It is the entry point for the level-lowering statements [`WeierstrassCurve.isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf) and [`WeierstrassCurve.isResiduallyModularOfLevel_div_of_isPeuRamifieeAt`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_div_of_isPeuRamifieeAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isEigenformIdeal_of_isResiduallyModularOfLevel.lean

import Mathlib
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_ModularCurve_EigenformIdeal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_isEigenformIdeal_of_isResiduallyModularOfLevel
    (W : WeierstrassCurve ℤ) {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 0 < N)
    (hmod : W.IsResiduallyModularOfLevel p N) :
    ∃ 𝔪 : Ideal ModularCurve.HeckeAlg, ModularCurve.IsEigenformIdeal N 𝔪 ∧
      (p : ModularCurve.HeckeAlg) ∈ 𝔪 ∧
      ∀ ℓ : Nat.Primes, W.IsGoodPrimeFor ℓ → ¬ (ℓ : ℕ) ∣ N → (ℓ : ℕ) ≠ p →
        ModularCurve.heckeGen ℓ - MvPolynomial.C (W.apOfModel ℓ) ∈ 𝔪 := by sorry
