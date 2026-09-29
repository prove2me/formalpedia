-- Prove2me | Theorems.Thm_HopfAlgebra_exists_connected_etale_sequence_padicInt
-- name    : HopfAlgebra.exists_connected_etale_sequence_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/66291546-6110-565f-af2c-7f07c2b4ae41
-- title:
--   Connected–étale sequence over ℤₚ in Hopf-algebraic form
-- statement:
--   Fix a prime $p$ and let $H$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}_p$ which is finite and free as a $\mathbb{Z}_p$-module and whose comultiplication is cocommutative. The assertion is the existence of two further commutative rings $H_0$ and $H_e$, each with a $\mathbb{Z}_p$-Hopf algebra structure, together with bialgebra homomorphisms $\pi : H \to H_0$ and $\iota : H_e \to H$ over $\mathbb{Z}_p$, such that: $H_0$ is finite and free over $\mathbb{Z}_p$, cocommutative, and a local ring; $H_e$ is finite and free over $\mathbb{Z}_p$, cocommutative, and étale over $\mathbb{Z}_p$; $\pi$ is surjective with $\ker \pi = (e)$ for some idempotent $e \in H$; $\iota$ is injective and its image is exactly the Hopf kernel of $\pi$, i.e. the subalgebra of those $x \in H$ with $(\mathrm{id}_H \otimes \pi)(\Delta x) = x \otimes 1$ in $H \otimes_{\mathbb{Z}_p} H_0$; the ranks satisfy $\operatorname{rank} H = \operatorname{rank} H_0 \cdot \operatorname{rank} H_e$; the number of $\mathbb{Z}_p$-algebra homomorphisms $H_e \to \overline{\mathbb{Q}}_p$ (the algebraic closure `PadicAlgCl p`) equals $\operatorname{rank}_{\mathbb{Z}_p} H_e$; a $\mathbb{Z}_p$-algebra map $f : H \to \overline{\mathbb{Q}}_p$ satisfies $f \circ \iota = \varepsilon_{H_e}$ followed by $\mathbb{Z}_p \to \overline{\mathbb{Q}}_p$ precisely when $f$ factors as $g \circ \pi$ for some $g : H_0 \to \overline{\mathbb{Q}}_p$; every $h : H_e \to \overline{\mathbb{Q}}_p$ is of the form $f \circ \iota$; and every automorphism $\sigma$ of $\overline{\mathbb{Q}}_p$ over $\mathbb{Q}_p$ lying in the inertia subgroup attached to the valuation subring of $\overline{\mathbb{Q}}_p$ (the image of the inertia subgroup inside the decomposition subgroup) fixes $h(y)$ for all such $h$ and all $y \in H_e$.
--
--   This is the connected–étale sequence of a finite flat commutative group scheme $G = \operatorname{Spec} H$ over $\mathbb{Z}_p$, stated entirely in terms of Hopf algebras: $H_0$ corresponds to the connected component $G^0$, cut out by an idempotent, and $H_e$ to the étale quotient $G/G^0$, whose $\overline{\mathbb{Q}}_p$-points are unramified and form the quotient of $G(\overline{\mathbb{Q}}_p)$ by $G^0(\overline{\mathbb{Q}}_p)$. It is used in the construction of connected and unipotent models for residual Galois representations at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_connected_etale_sequence_padicInt.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped PadicInt

theorem HopfAlgebra.exists_connected_etale_sequence_padicInt
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Free ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H] :
    ∃ (H₀ : Type) (_ : CommRing H₀) (_ : HopfAlgebra ℤ_[p] H₀) (Hₑ : Type) (_ : CommRing Hₑ)
      (_ : HopfAlgebra ℤ_[p] Hₑ) (π : H →ₐc[ℤ_[p]] H₀) (ι : Hₑ →ₐc[ℤ_[p]] H),
      Module.Finite ℤ_[p] H₀ ∧ Module.Free ℤ_[p] H₀ ∧ Coalgebra.IsCocomm ℤ_[p] H₀ ∧ IsLocalRing H₀ ∧
      Module.Finite ℤ_[p] Hₑ ∧ Module.Free ℤ_[p] Hₑ ∧ Coalgebra.IsCocomm ℤ_[p] Hₑ ∧
        Algebra.Etale ℤ_[p] Hₑ ∧
      Function.Surjective π ∧ (∃ e : H, IsIdempotentElem e ∧ RingHom.ker π = Ideal.span {e}) ∧
      Function.Injective ι ∧ (∀ x : H, x ∈ HopfAlgebra.hopfKer π ↔ x ∈ Set.range ι) ∧
      Module.finrank ℤ_[p] H = Module.finrank ℤ_[p] H₀ * Module.finrank ℤ_[p] Hₑ ∧
      Nat.card (Hₑ →ₐ[ℤ_[p]] PadicAlgCl p) = Module.finrank ℤ_[p] Hₑ ∧
      (∀ f : H →ₐ[ℤ_[p]] PadicAlgCl p,
        f.comp (ι : Hₑ →ₐ[ℤ_[p]] H) =
            (Algebra.ofId ℤ_[p] (PadicAlgCl p)).comp (Bialgebra.counitAlgHom ℤ_[p] Hₑ) ↔
          ∃ g : H₀ →ₐ[ℤ_[p]] PadicAlgCl p, f = g.comp (π : H →ₐ[ℤ_[p]] H₀)) ∧
      (∀ h : Hₑ →ₐ[ℤ_[p]] PadicAlgCl p, ∃ f : H →ₐ[ℤ_[p]] PadicAlgCl p,
        f.comp (ι : Hₑ →ₐ[ℤ_[p]] H) = h) ∧
      (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (padicIntegers p).inertiaSubgroupIn ℚ_[p] →
        ∀ (h : Hₑ →ₐ[ℤ_[p]] PadicAlgCl p) (y : Hₑ), σ (h y) = h y) := by sorry
