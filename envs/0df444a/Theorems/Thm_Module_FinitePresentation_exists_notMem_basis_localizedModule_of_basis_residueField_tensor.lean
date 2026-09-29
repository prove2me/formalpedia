-- Prove2me | Theorems.Thm_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor
-- name    : Module.FinitePresentation.exists_notMem_basis_localizedModule_of_basis_residueField_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/b07c97f6-d16a-5d1d-a006-7a15c3fe18c3
-- title:
--   Spreading a fibre basis to a basic open neighbourhood
-- statement:
--   Let $T$ be a commutative ring and $M$ a $T$-module (carried by an additive commutative group) which is of finite presentation over $T$, both in a fixed universe. Let $\mathfrak p$ be a prime ideal of $T$ and assume that the corresponding point $\langle \mathfrak p\rangle$ of $\operatorname{Spec} T$ lies in `Module.freeLocus T M`, i.e. the localisation of $M$ at $\mathfrak p$ is a free module over $T_{\mathfrak p}$. Let $\iota$ be a finite type, let $m : \iota \to M$ be a family of elements of $M$, and let $b$ be a basis of the fibre $\kappa(\mathfrak p) \otimes_T M$ over the residue field $\kappa(\mathfrak p)$ of $\mathfrak p$, indexed by $\iota$, such that $b_i = 1 \otimes m_i$ for every $i$. Then there exist an element $t \in T$ with $t \notin \mathfrak p$ and a basis $b'$ of the localised module $M[t^{-1}]$ over the localisation $T[t^{-1}]$ (formed at the submonoid of powers of $t$), again indexed by $\iota$, such that $b'_i$ is the image of $m_i$ under the canonical map $M \to M[t^{-1}]$ for every $i$.
--
--   This is the standard spreading-out statement that a family of elements of a finitely presented module whose residues form a basis of the fibre at a prime in the free locus already forms a basis over some basic open neighbourhood of that prime (EGA $0_{IV}$ 19.1.12). It is used in the construction of a smooth presentation with a prescribed basis of the module of Kähler differentials, via [`Algebra.exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span`](thm.html#Algebra.exists_smooth_surjective_localizationAway_basis_kaehlerDifferential_comap_eq_span).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_FinitePresentation_exists_notMem_basis_localizedModule_of_basis_residueField_tensor.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

universe u

theorem Module.FinitePresentation.exists_notMem_basis_localizedModule_of_basis_residueField_tensor
    {T : Type u} [CommRing T] {M : Type u} [AddCommGroup M] [Module T M] [Module.FinitePresentation T M]
    (p : Ideal T) [hp : p.IsPrime] (hfree : (⟨p, hp⟩ : PrimeSpectrum T) ∈ Module.freeLocus T M)
    {ι : Type} [Finite ι] (m : ι → M)
    (b : Module.Basis ι p.ResidueField (p.ResidueField ⊗[T] M)) (hb : ∀ i, b i = (1 : p.ResidueField) ⊗ₜ[T] m i) :
    ∃ (t : T) (_ : t ∉ p)
      (b' : Module.Basis ι (Localization.Away t) (LocalizedModule (Submonoid.powers t) M)),
      ∀ i, b' i = LocalizedModule.mkLinearMap (Submonoid.powers t) M (m i) := by sorry
