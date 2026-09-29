-- Prove2me | Theorems.Thm_ModularCurve_residualRealization_of_occurs
-- name    : ModularCurve.residualRealization_of_occurs
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/3f73b3ba-647e-580e-bd56-15466de73508
-- title:
--   Residual realization attached to an occurring Hecke eigensystem
-- statement:
--   Let $M \ge 1$ and let $p$ be a prime, and equip $J_0(M) :=$ [`ModularCurve.JZero M`](def/ModularCurve_ArithmeticGalois.html#L115), the group of degree-zero divisor classes of the modular function field of level $M$ base-changed to $\overline{\mathbb{Q}}$, with the module structure [`ModularCurve.heckeModuleBar M`](def/ModularCurve_HeckeModule.html#L82) over the abstract Hecke algebra $\mathbb{T} = \mathbb{Z}[T_\ell : \ell \text{ prime}]$ (the polynomial ring over $\mathbb{Z}$ on the set of primes). The assertion is: for every algebraically closed field $k$ and every ring homomorphism $\varphi : \mathbb{T} \to k$ such that $p = 0$ in $k$, $\mathfrak{m} := \ker \varphi$ is a maximal ideal, and the $\mathfrak{m}$-torsion submodule $\{x \in J_0(M) : \mathfrak{m}x = 0\}$ is nonzero, there exist a $k$-vector space $V$, a map $\pi : J_0(M) \to V$, a homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{GL}(V)$ (as $k$-linear automorphisms), and a number field $F$, Galois over $\mathbb{Q}$ and realised as an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$, with the following three properties. First, [`ModularCurve.IsResidualRealization`](def/ModularCurve_ResidualRealization.html#L21) holds for $(p, J_0(M), k, \varphi, V, \pi, \rho)$: $V$ is finite over $k$ of dimension exactly $2$; $\pi(0) = 0$; $\pi(x+y) = \pi x + \pi y$, $\pi(\sigma \cdot x) = \rho(\sigma)(\pi x)$ and $\pi(t \cdot x) = \varphi(t)\,\pi x$ whenever $x$ (and $y$) are killed by $p$, for all $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and $t \in \mathbb{T}$; and the image $\pi(J_0(M)[p])$ spans $V$ over $k$. Second, [`ModularCurve.CyclotomicDeterminant M p ρ`](def/ModularCurve_ResidualRealization.html#L44): for every prime $\ell \nmid Mp$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, and every $\sigma$ lying in the decomposition subgroup of $A$ and inducing $x \mapsto x^{\ell}$ on the residue field of $A$, one has $\det \rho(\sigma) = \ell$ in $k$. Third, $\rho$ is trivial on the kernel of the restriction map $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{Gal}(F/\mathbb{Q})$, so $\rho$ factors through $\mathrm{Gal}(F/\mathbb{Q})$.
--
--   This is the residual (mod $p$) form of the Eichler–Shimura construction: a Hecke eigensystem $\varphi$ occurring in the $\mathfrak{m}$-torsion of the Jacobian of $X_0(M)$ gives rise to a two-dimensional mod-$p$ Galois representation with cyclotomic determinant, cut out by $\varphi$ on $J_0(M)[p]$ through $\pi$ and ramified only within a finite Galois number field $F$. It is used by [`FreyPackage.eigenformRealizationSupplyFieldAtFamily`](thm.html#FreyPackage.eigenformRealizationSupplyFieldAtFamily) to supply the mod-$p$ representations attached to eigenforms in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_residualRealization_of_occurs.lean

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_ResidualRealization
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.residualRealization_of_occurs (M p : ℕ) [NeZero M] [Fact p.Prime] :
    letI := ModularCurve.heckeModuleBar M;
    ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : ModularCurve.HeckeAlg →+* k),
      (p : k) = 0 → (RingHom.ker φ).IsMaximal →
      ModularCurve.heckeTorsion (ModularCurve.JZero M) (RingHom.ker φ) ≠ ⊥ →
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module k V)
        (π : ModularCurve.JZero M → V)
        (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (V ≃ₗ[k] V))
        (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
        (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
        ModularCurve.IsResidualRealization p (ModularCurve.JZero M) k φ V π ρ ∧
        ModularCurve.CyclotomicDeterminant M p ρ ∧
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρ.ker := by sorry
