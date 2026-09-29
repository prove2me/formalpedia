-- Prove2me | Theorems.Thm_M4aHerbrand_sUnitQuot_fixedRank_eq
-- name    : M4aHerbrand.sUnitQuot_fixedRank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/a79aba0b-9b3c-5efa-a9f9-71e5c36e0521
-- title:
--   Fixed ranks of S-units, finite places and infinite places
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $\sigma$ be a $K$-automorphism of $L$, and let $S$ be a finite set of non-zero prime ideals of $\mathcal{O}_K$. Let $W$ be the set of height-one primes $w$ of $\mathcal{O}_L$ whose contraction to $\mathcal{O}_K$ lies in $S$, and let $W.\mathrm{unit}\ L \le L^\times$ be the corresponding group of $W$-units. The Galois action is pinned down by abstract data together with characterising hypotheses: $\Phi$ is a multiplicative automorphism of the $W$-unit group with $\Phi(u) = \sigma(u)$ as elements of $L$; $T$ is an additive subgroup of the additive version of that group consisting exactly of the elements $x$ for which $n \cdot x = 0$ for some $n \neq 0$, i.e. the torsion subgroup; $\psi$ is an additive automorphism of the quotient by $T$ sending the class of $u$ to the class of $\Phi(u)$; $\pi$ is a permutation of $W$ with $(\pi w)$ the ideal-theoretic image of $w$ under the restriction of $\sigma$ to $\mathcal{O}_L$, and $\pi_\ell$ the automorphism $f \mapsto f \circ \pi^{-1}$ of $\mathbb{Z}^{W}$; $\rho$ is the permutation $v \mapsto v \circ \sigma^{-1}$ of the infinite places of $L$, and $\rho_\ell$ the automorphism $f \mapsto f \circ \rho^{-1}$ of $\mathbb{Z}^{\mathrm{InfinitePlace}\,L}$. The conclusion is that for every natural number $e$,
--   $$\operatorname{rk}_{\mathbb{Z}} \ker(\psi^{e} - \mathrm{id}) + 1 = \operatorname{rk}_{\mathbb{Z}} \ker(\pi_\ell^{\,e} - \mathrm{id}) + \operatorname{rk}_{\mathbb{Z}} \ker(\rho_\ell^{\,e} - \mathrm{id}),$$
--   each kernel being taken of the associated $\mathbb{Z}$-linear endomorphism and each rank being `Module.finrank ℤ`.
--
--   This is the Dirichlet $S$-unit theorem in equivariant form, evaluated on the fixed parts of $\sigma^{e}$: the unit lattice sits with corank one inside the permutation lattice on the places in $W$ together with the infinite places, and taking $\sigma^{e}$-invariants costs exactly one in rank. It feeds the computation of Herbrand quotients of $S$-unit groups in a cyclic extension, and is cited here by [`M4aHerbrand.sUnit_tateCard_mul_localDegreeProd`](thm.html#M4aHerbrand.sUnit_tateCard_mul_localDegreeProd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_sUnitQuot_fixedRank_eq.lean

import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem M4aHerbrand.sUnitQuot_fixedRank_eq
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

    (W : Set (HeightOneSpectrum (𝓞 L))) (hW : W = {w | w.under (𝓞 K) ∈ ↑S})

    (Φ : ↥(W.unit L) ≃* ↥(W.unit L))
    (hΦ : ∀ u, (((Φ u : Lˣ) : L)) = σ (((u : Lˣ) : L)))

    (T : AddSubgroup (Additive ↥(W.unit L)))
    (hT : ∀ x, x ∈ T ↔ ∃ n : ℕ, n ≠ 0 ∧ n • x = 0)

    (ψ : AddAut (Additive ↥(W.unit L) ⧸ T))
    (hψ : ∀ u, ψ (QuotientAddGroup.mk (Additive.ofMul u))
          = QuotientAddGroup.mk (Additive.ofMul (Φ u)))

    (π : Equiv.Perm ↥W)
    (hπ : ∀ w, (π w).1.asIdeal = Ideal.map ((galRestrict (𝓞 K) K L (𝓞 L)) σ) w.1.asIdeal)
    (πl : AddAut (↥W → ℤ)) (hπl : ∀ f w, πl f w = f (π.symm w))

    (ρ : Equiv.Perm (InfinitePlace L)) (hρ : ∀ v, ρ v = v.comap (σ.symm : L →+* L))
    (ρl : AddAut (InfinitePlace L → ℤ)) (hρl : ∀ f v, ρl f v = f (ρ.symm v)) :
    ∀ e : ℕ,
      Module.finrank ℤ ↥(LinearMap.ker (((ψ ^ e) : AddAut _).toAddMonoidHom.toIntLinearMap - LinearMap.id)) + 1
        = Module.finrank ℤ ↥(LinearMap.ker (((πl ^ e) : AddAut _).toAddMonoidHom.toIntLinearMap - LinearMap.id))
          + Module.finrank ℤ ↥(LinearMap.ker (((ρl ^ e) : AddAut _).toAddMonoidHom.toIntLinearMap - LinearMap.id)) := by sorry
