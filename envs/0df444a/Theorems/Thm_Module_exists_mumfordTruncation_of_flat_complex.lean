-- Prove2me | Theorems.Thm_Module_exists_mumfordTruncation_of_flat_complex
-- name    : Module.exists_mumfordTruncation_of_flat_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/43f35493-f4d2-5159-8bce-df1ab9216f22
-- title:
--   Mumford's truncation of a bounded flat complex
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $C^\bullet$ be a complex of $R$-modules indexed by $\mathbb{N}$, given by modules $C^i$ that are flat over $R$ and maps $d^i\colon C^i\to C^{i+1}$ with $d^{i+1}\circ d^i=0$; assume there is $n$ with $C^i$ subsingleton (that is, zero) for all $i>n$, that $\ker d^0$ is a finite $R$-module, and that for every $i$ the quotient of $\ker d^{i+1}$ by the preimage of $\operatorname{im} d^i$ under the inclusion of $\ker d^{i+1}$ — i.e. $H^{i+1}(C^\bullet)$ — is a finite $R$-module. Then there exist $m_0,m_1\in\mathbb{N}$, an $R$-submodule $P\subseteq C^0\times R^{m_0}$ which is finite and flat over $R$, and an $R$-linear map $\varepsilon\colon R^{m_0}\to R^{m_1}$ such that, writing $\delta\colon P\to R^{m_0}$ for the second projection restricted to $P$, one has $\varepsilon\circ\delta=0$ and, for every commutative $R$-algebra $A$: (i) if $\ker(d^1\otimes_R A)\subseteq\operatorname{im}(d^0\otimes_R A)$ then $\ker(\varepsilon\otimes_R A)\subseteq\operatorname{im}(\delta\otimes_R A)$; (ii) if the image of $(\ker\delta)\otimes_R A\to P\otimes_R A$ equals $\ker(\delta\otimes_R A)$, then the image of $(\ker d^0)\otimes_R A\to C^0\otimes_R A$ equals $\ker(d^0\otimes_R A)$; (iii) if $(\ker\delta)\otimes_R A\to P\otimes_R A$ is injective, then so is $(\ker d^0)\otimes_R A\to C^0\otimes_R A$.
--
--   This is Mumford's truncation lemma in the form used for cohomology and base change in degree $0$: the vanishing of $H^1$ after base change is transported from the given bounded flat complex to a length-two complex $P\to R^{m_0}\to R^{m_1}$ with $P$ finite and flat, while the statement that forming $H^0$ commutes with the base change $R\to A$ is transported back. It is the reduction step behind [`Module.ker_baseChange_field_of_subsingleton_H1`](thm.html#Module.ker_baseChange_field_of_subsingleton_H1), where the corresponding assertion for the truncated complex is a question about maps of finite projective modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_mumfordTruncation_of_flat_complex.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_MumfordTruncation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open TensorProduct

theorem Module.exists_mumfordTruncation_of_flat_complex
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)) :
    ∃ (m₀ m₁ : ℕ) (P : Submodule R (C 0 × (Fin m₀ → R))) (ε : (Fin m₀ → R) →ₗ[R] (Fin m₁ → R)),
      Module.Finite R P ∧ Module.Flat R P ∧
      ε ∘ₗ (LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype) = 0 ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        (LinearMap.ker ((d 1).baseChange A) ≤ LinearMap.range ((d 0).baseChange A) →
          LinearMap.ker (ε.baseChange A)
            ≤ LinearMap.range ((LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype).baseChange A)) ∧
        (LinearMap.range ((LinearMap.ker (LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype)).subtype.baseChange A)
            = LinearMap.ker ((LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype).baseChange A) →
          LinearMap.range ((LinearMap.ker (d 0)).subtype.baseChange A) = LinearMap.ker ((d 0).baseChange A)) ∧
        (Function.Injective
            ((LinearMap.ker (LinearMap.snd R (C 0) (Fin m₀ → R) ∘ₗ P.subtype)).subtype.baseChange A) →
          Function.Injective ((LinearMap.ker (d 0)).subtype.baseChange A)) := by sorry
