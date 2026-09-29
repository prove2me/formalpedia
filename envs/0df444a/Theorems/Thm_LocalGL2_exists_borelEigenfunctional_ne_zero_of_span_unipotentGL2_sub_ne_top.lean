-- Prove2me | Theorems.Thm_LocalGL2_exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top
-- name    : LocalGL2.exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/4206025c-069a-5e36-ab64-3c0b425eae5e
-- title:
--   Non-cuspidal irreducible admissible GL₂(Kᵥ) representations admit Borel eigenfunctionals
-- statement:
--   Let $K$ be a number field, let $v$ be a prime of the ring of integers $\mathcal{O}_K$ (a point of its height-one spectrum), and write $K_v$ for the $v$-adic completion. Let $V$ be a complex vector space and $\pi : GL_2(K_v) \to \operatorname{End}_{\mathbf C}(V)$ a monoid homomorphism, assumed: smooth, in the sense that for every $w \in V$ the subgroup $\{g : \pi(g)w = w\}$ is open; admissible, in the sense that for every compact open subgroup $H$ the space of vectors fixed by all of $H$ is finite-dimensional over $\mathbf C$; and irreducible, in the sense that $V$ contains a nonzero vector and every $\pi$-stable subspace is $0$ or $V$. Write $n(t) = \begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix}$ and $\operatorname{diag}(a,1)$ for the indicated elements of $GL_2(K_v)$. Assume the $\mathbf C$-span of $\{\pi(n(t))z - z : t \in K_v,\, z \in V\}$ is not all of $V$. Then there are group homomorphisms $\chi, \omega : K_v^\times \to \mathbf C^\times$ and a nonzero $\mathbf C$-linear functional $\ell : V \to \mathbf C$ with $\ell(\pi(n(x))w) = \ell(w)$, $\ell(\pi(\operatorname{diag}(a,1))w) = \chi(a)\ell(w)$ and $\ell(\pi(aI_2)w) = \omega(a)\ell(w)$ for all $x \in K_v$, $a \in K_v^\times$, $w \in V$.
--
--   The hypothesis says that the Jacquet module $V/V(N)$ of $\pi$ with respect to the upper triangular unipotent subgroup is nonzero, i.e. that $\pi$ is not cuspidal; the conclusion produces a functional on which the Borel subgroup acts by a character, equivalently an embedding of $\pi$ into a principal series. It is used in the Rankin–Selberg part of the Langlands–Tunnell argument, where the local components of an automorphic representation are split into the cuspidal case, treated via Kirillov models, and the non-cuspidal case treated here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top.lean

import Mathlib
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField
open FLT.SmoothAdmissibleSchurCommutant

theorem LocalGL2.exists_borelEigenfunctional_ne_zero_of_span_unipotentGL2_sub_ne_top
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : GL (Fin 2) (v.adicCompletion K) →* Module.End ℂ V)
    (hsm : IsSmoothRep π) (hadm : IsAdmissibleRep π) (hirr : IsIrreducibleRep π)
    (hN : Submodule.span ℂ {y : V | ∃ (t : v.adicCompletion K) (z : V),
      y = π (AutomorphicForm.unipotentGL2 t) z - z} ≠ ⊤) :
    ∃ (χ ω : (v.adicCompletion K)ˣ →* ℂˣ) (ℓ : V →ₗ[ℂ] ℂ), ℓ ≠ 0 ∧
      (∀ (x : v.adicCompletion K) (w : V), ℓ (π (AutomorphicForm.unipotentGL2 x) w) = ℓ w) ∧
      (∀ (a : (v.adicCompletion K)ˣ) (w : V), ℓ (π (AdelicLevel.diagOne a) w) = χ a * ℓ w) ∧
      (∀ (a : (v.adicCompletion K)ˣ) (w : V),
        ℓ (π (Matrix.GeneralLinearGroup.scalar (Fin 2) a) w) = ω a * ℓ w) := by sorry
