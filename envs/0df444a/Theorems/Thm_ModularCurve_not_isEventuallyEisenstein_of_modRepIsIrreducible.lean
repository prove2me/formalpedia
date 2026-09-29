-- Prove2me | Theorems.Thm_ModularCurve_not_isEventuallyEisenstein_of_modRepIsIrreducible
-- name    : ModularCurve.not_isEventuallyEisenstein_of_modRepIsIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/9de48870-2227-51fa-8d64-c8ce340794e8
-- title:
--   Irreducible mod p representations give non-Eisenstein Hecke ideals
-- statement:
--   Let $p$ be a prime, let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$, and assume `W.ModRepIsIrreducible p`: the $p$-torsion of the group of points of the affine model of $W$ base-changed to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` is nontrivial, and every $\mathbb{Z}/p$-submodule of it that is stable under the $\mathbb{Q}$-automorphisms of $\overline{\mathbb{Q}}$ is $\bot$ or $\top$. Let $S_0 \subseteq \mathbb{N}$ be finite, let $i \in \mathbb{N}$ satisfy $(p-1) \mid 2i$ (truncated subtraction), and let $\mathfrak{m}$ be an ideal, distinct from the unit ideal, of the polynomial ring `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$ in indeterminates `heckeGen ℓ` indexed by the primes, such that $p \in \mathfrak{m}$ and such that for every prime $\ell \notin S_0$ with $\ell \nmid \Delta_W$ one has $X_\ell - \ell^{i} a_\ell(W) \in \mathfrak{m}$, where $a_\ell(W) = \ell + 1 - \#(W \bmod \ell)$ is `W.apOfModel ℓ`. Then $\mathfrak{m}$ is not eventually Eisenstein: there is no finite set $S$ of primes such that $X_\ell - (\ell + 1) \in \mathfrak{m}$ for all primes $\ell \notin S$.
--
--   This is the non-Eisenstein property of the mod $p$ system of Hecke eigenvalues attached to an elliptic curve with irreducible mod $p$ representation, in the twisted form allowing a cyclotomic shift $\ell^{i}$ with $(p-1) \mid 2i$, as used by Mazur and Ribet. It feeds the level-lowering arguments of the project: it is invoked when realising the mod $p$ representation of a Frey curve inside Hecke modules and in the construction of eigenform congruences at lowered level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_not_isEventuallyEisenstein_of_modRepIsIrreducible.lean

import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_ModularCurve_MazurPrincipleCore

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.not_isEventuallyEisenstein_of_modRepIsIrreducible (p : ℕ) [Fact p.Prime]
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hirr : W.ModRepIsIrreducible p)
    (S₀ : Set ℕ) (hS₀fin : S₀.Finite) (i : ℕ) (hi : (p - 1) ∣ 2 * i)
    (𝔪 : Ideal HeckeAlg) (h𝔪 : 𝔪 ≠ ⊤) (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (hcong : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S₀ → W.IsGoodPrimeFor ℓ →
      heckeGen ⟨ℓ, hℓ⟩ - ((ℓ ^ i * W.apOfModel ℓ : ℤ) : HeckeAlg) ∈ 𝔪) :
    ¬ IsEventuallyEisenstein 𝔪 := by sorry
