-- Prove2me | Theorems.Thm_HeckeCohomology_exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact
-- name    : HeckeCohomology.exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/43591a0c-9eef-5add-8391-f62b3e4a8e59
-- title:
--   Pushing H¹ Hecke eigenclasses forward, or the Eisenstein alternative
-- statement:
--   Let $\kappa$ be a field, $\Gamma$ a group, and let $X$ be a short complex $X_1 \to X_2 \to X_3$ in $\mathrm{Rep}\,\kappa\,\Gamma$ which is short exact. Let $\iota$ be an index type, and for each $i \in \iota$ let $S_1(i), S_2(i)$ be subgroups of $\Gamma$ with $S_2(i)$ of finite index, together with a group homomorphism $c_i : S_2(i) \to S_1(i)$. For each $i$ let $\varphi_1(i), \varphi_2(i), \varphi_3(i)$ be $\kappa$-linear endomorphisms of the underlying modules of $X_1, X_2, X_3$, each a twist in the sense that $\varphi(\rho(c_i(s))a) = \rho(s)(\varphi(a))$ for all $s \in S_2(i)$ and all $a$ in the relevant representation; assume the maps of $X$ intertwine them, i.e. $f(\varphi_1(i)a) = \varphi_2(i)(f(a))$ and $g(\varphi_2(i)b) = \varphi_3(i)(g(b))$ for all $i$. Let $cc : \iota \to \kappa$ be such that for each $i$ the operator `heckeInv` on the invariants $X_3^{\Gamma}$ — the restriction to invariants of the averaging map $a \mapsto \sum_q \rho(\mathrm{rep}\,q)^{-1}(\varphi_3(i)a)$ over the right cosets of $S_2(i)$ — acts as multiplication by $cc(i)$. Let $lam : \iota \to \kappa$, and suppose there is a nonzero $x \in H^1(\Gamma, X_1)$ with `heckeH1` for $(S_1(i), S_2(i), c_i, \varphi_1(i))$ sending $x$ to $lam(i)\,x$ for every $i$. Then either there is a nonzero $y \in H^1(\Gamma, X_2)$ with `heckeH1` for $(S_1(i), S_2(i), c_i, \varphi_2(i))$ sending $y$ to $lam(i)\,y$ for every $i$, or $lam(i) = cc(i)$ for every $i$. (The conclusion does not record that $y$ may be taken to be the image of $x$.)
--
--   This is the dichotomy used to transport a simultaneous eigenclass for a family of transfer Hecke operators from $H^1$ of a subrepresentation to $H^1$ of the ambient representation, the alternative being that the eigenvalue system coincides with the system on the invariants of the quotient (the Eisenstein case). It is applied in the dévissage producing the Eisenstein alternative for eigensystems attached to a Steinberg quotient, where the conclusion either yields an eigenvector upstairs or pins the eigenvalues down to the scalars $cc(i)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCohomology_exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact.lean

import Mathlib
import Definitions.Def_GroupCohomology_TransferHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HeckeCohomology.exists_eigenvector_H1_or_forall_eq_of_eigenvector_H1_of_shortExact
    {κ Γ : Type} [Field κ] [Group Γ]
    {X : CategoryTheory.ShortComplex (Rep κ Γ)} (hX : X.ShortExact)
    {ι : Type} (S₁ S₂ : ι → Subgroup Γ) (c : ∀ i, ↥(S₂ i) →* ↥(S₁ i)) [∀ i, (S₂ i).FiniteIndex]
    (φ₁ : ∀ i, X.X₁ →ₗ[κ] X.X₁) (hφ₁ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₁ (φ₁ i))
    (φ₂ : ∀ i, X.X₂ →ₗ[κ] X.X₂) (hφ₂ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i))
    (φ₃ : ∀ i, X.X₃ →ₗ[κ] X.X₃) (hφ₃ : ∀ i, HeckeCohomology.IsTwist (S₁ i) (S₂ i) (c i) X.X₃ (φ₃ i))
    (hf : ∀ (i : ι) (a : X.X₁), X.f.hom (φ₁ i a) = φ₂ i (X.f.hom a))
    (hg : ∀ (i : ι) (b : X.X₂), X.g.hom (φ₂ i b) = φ₃ i (X.g.hom b))
    (cc : ι → κ)
    (hinv : ∀ (i : ι) (z : X.X₃.ρ.invariants),
      HeckeCohomology.heckeInv (S₁ i) (S₂ i) (c i) X.X₃ (φ₃ i) (hφ₃ i) z = cc i • z)
    (lam : ι → κ)
    (hocc : ∃ x : groupCohomology.H1 X.X₁, x ≠ 0 ∧
      ∀ i : ι, HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₁ (φ₁ i) (hφ₁ i) x = lam i • x) :
    (∃ y : groupCohomology.H1 X.X₂, y ≠ 0 ∧
      ∀ i : ι, HeckeCohomology.heckeH1 (S₁ i) (S₂ i) (c i) X.X₂ (φ₂ i) (hφ₂ i) y = lam i • y) ∨
    ∀ i : ι, lam i = cc i := by sorry
