-- Prove2me | Theorems.Thm_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range
-- name    : ModularCurve.finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/2a191cfe-ea54-58bd-9d46-f71f93bedfb0
-- title:
--   Toric 𝔪-torsion bounded via a character lattice sandwich
-- statement:
--   Fix a prime $p$, a nonzero natural number $M$, a natural number $r$ with $p \neq r$, and a valuation subring $A$ of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $r$, in the sense that $r$ is a nonunit of $A$; write $I =$ `A.inertiaSubgroupIn ℚ` for the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $A$ under the inclusion of its decomposition subgroup, and $k$ for the residue field of $A$. Let $J =$ `JZero M` be the degree-zero divisor class group of the level-$M$ modular function field over $\overline{\mathbb Q}$, equipped with the Hecke-algebra structure `heckeModuleBar M` over $\mathbb{T} =$ `HeckeAlg` $= \mathbb Z[X_\ell : \ell \text{ prime}]$, and let $\mathcal T \subseteq J$ be the $\mathbb{T}$-submodule spanned by the elements $\sigma \cdot x - x$ with $\sigma \in I$ and $x \in J$ killed by some $m > 0$ coprime to $r$. Let $\mathfrak m \subset \mathbb T$ be a maximal ideal containing $p$. Let $\iota_1$ be a finite type, $X_1 =$ `characterLattice ι₁` the kernel of the total-degree map $(\iota_1 \to \mathbb Z) \to \mathbb Z$, and for each prime $\ell$ let $T_1(\ell)$ be an integer $\iota_1 \times \iota_1$ matrix whose transpose has all row sums equal to $n_1(\ell)$, so that the transpose acts on $X_1$ by `heckeCharacterAction`. Assume given an additive isomorphism $\varepsilon_1 : \mathcal T \xrightarrow{\sim} \mathrm{Hom}(X_1, \mathrm{Additive}\, k^\times)$ with $\varepsilon_1(X_\ell \cdot y)(x) = \varepsilon_1(y)(T_1(\ell)^{\mathsf T} x)$ for all primes $\ell$, all $y \in \mathcal T$ and all $x \in X_1$. Assume further given $\mathbb T$-modules $Q$ and $L$, each finitely generated over $\mathbb Z$, an additive map $\varphi : Q \to X_1$ with $\varphi(X_\ell \cdot z) = T_1(\ell)^{\mathsf T}\varphi(z)$, and a surjective additive map $\pi : X_1 \to L$ with $\pi(T_1(\ell)^{\mathsf T} x) = X_\ell \cdot \pi(x)$, such that every $x \in X_1$ with $\pi(x) = 0$ lies in the image of $\varphi$. Then the $\mathbb T/\mathfrak m$-dimension of the $\mathbb T/\mathfrak m$-span, inside the $\mathfrak m$-torsion $J[\mathfrak m] =$ `heckeTorsion (JZero M) 𝔪`, of the set of its elements lying in $\mathcal T$ is at most $\dim_{\mathbb T/\mathfrak m} L/\mathfrak m L + \dim_{\mathbb T/\mathfrak m} Q/\mathfrak m Q$.
--
--   This is the character-group estimate underlying Ribet's level-lowering argument: the toric part of the $r$-adic monodromy on the Jacobian is measured by a character lattice, and an exact-sequence sandwich $Q \to X_1 \twoheadrightarrow L$ of Hecke-compatible lattices converts the duality statement into a bound with an error term coming from $Q$. It is the form in which the estimate is applied in the two results deducing the bound for a supersingular level datum from an anchoring of the toric part, and it is obtained from the exact duality statement [`RibetLevelLowering.finrank_span_torsion_eq_finrank_quotient_of_characterDuality`](thm.html#RibetLevelLowering.finrank_span_torsion_eq_finrank_quotient_of_characterDuality) together with the algebraic closedness of the residue field of a valuation subring of $\overline{\mathbb Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ComponentGroupHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem
    ModularCurve.finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range
    (p : ℕ) [Fact p.Prime] {M : ℕ} [NeZero M] (r : ℕ) (hpr : p ≠ r)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    {ι₁ : Type} [Fintype ι₁]
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hpm : (p : HeckeAlg) ∈ 𝔪)
    (T₁ : Nat.Primes → Matrix ι₁ ι₁ ℤ)
    (n₁ : Nat.Primes → ℤ) (hcol₁ : ∀ ℓ : Nat.Primes, HeckeRowSums (T₁ ℓ).transpose (n₁ ℓ))
    (ε₁ : letI := heckeModuleBar M;
      ↥(toricMonodromyPart (J := JZero M) r (A.inertiaSubgroupIn ℚ)) ≃+
        (↥(characterLattice ι₁) →+ Additive (IsLocalRing.ResidueField A)ˣ))
    (hε₁ : letI := heckeModuleBar M;
      ∀ (ℓ : Nat.Primes) (y : ↥(toricMonodromyPart (J := JZero M) r (A.inertiaSubgroupIn ℚ)))
        (x : ↥(characterLattice ι₁)),
        ε₁ (heckeGen ℓ • y) x = ε₁ y (heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) x))
    (Q : Type) [AddCommGroup Q] [Module HeckeAlg Q] [Module.Finite ℤ Q]
    (φ : Q →+ ↥(characterLattice ι₁))
    (hφT : ∀ (ℓ : Nat.Primes) (z : Q), φ (heckeGen ℓ • z) = heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) (φ z))
    (L : Type) [AddCommGroup L] [Module HeckeAlg L] [Module.Finite ℤ L]
    (πL : ↥(characterLattice ι₁) →+ L) (hπsurj : Function.Surjective πL)
    (hπT : ∀ (ℓ : Nat.Primes) (x : ↥(characterLattice ι₁)),
      πL (heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) x) = heckeGen ℓ • πL x)
    (hker : ∀ x : ↥(characterLattice ι₁), πL x = 0 → x ∈ AddMonoidHom.range φ) :
    letI := heckeModuleBar M
    Module.finrank (HeckeAlg ⧸ 𝔪)
        ↥(Submodule.span (HeckeAlg ⧸ 𝔪)
          ((Subtype.val : ↥(heckeTorsion (JZero M) 𝔪) → JZero M) ⁻¹'
            (toricMonodromyPart (J := JZero M) r (A.inertiaSubgroupIn ℚ) : Set (JZero M)))) ≤
      Module.finrank (HeckeAlg ⧸ 𝔪) (L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) +
        Module.finrank (HeckeAlg ⧸ 𝔪) (Q ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Q))) := by sorry
