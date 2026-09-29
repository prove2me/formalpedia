-- Prove2me | Theorems.Thm_NumberField_exists_isCyclic_algHom_cyclotomicField_mul_dvd_natCard_decomp_of_coprime
-- name    : NumberField.exists_isCyclic_algHom_cyclotomicField_mul_dvd_natCard_decomp_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/a3e2252a-f1ee-56ac-8058-9405f069ec7a
-- title:
--   Compositum of coprime cyclic cyclotomic layers with prescribed local degrees
-- statement:
--   Let $E$ be a number field and $T$ a finite set of height-one primes of $\mathcal{O}_E$. For $i = 1, 2$, let $n_i, m_i$ be natural numbers with $m_i \neq 0$, and let $F_i$ be a number field that is a Galois extension of $E$ with cyclic group $F_i \simeq_{\mathrm{alg}[E]} F_i$; assume there exists an $E$-algebra homomorphism $F_i \to \mathrm{CyclotomicField}\, m_i\, E$ (hypotheses `hcyc₁`, `hcyc₂`), that for every infinite place $w$ of $F_i$ the stabiliser of $w$ in $F_i \simeq_{\mathrm{alg}[E]} F_i$ is trivial, i.e. every $g$ fixing $w$ equals $1$ (`hinf₁`, `hinf₂`), that $n_i \mid \#(F_i \simeq_{\mathrm{alg}[E]} F_i)$, and that for every $v \in T$ and every height-one prime $w$ of $\mathcal{O}_{F_i}$ lying under $v$ (i.e. $w$ restricts to $v$ over $\mathcal{O}_E$) one has $n_i \mid \#D_w$, where $D_w$ is the decomposition subgroup of the valuation subring attached to $w$ inside $F_i \simeq_{\mathrm{alg}[E]} F_i$. Assume finally that $\#(F_1 \simeq_{\mathrm{alg}[E]} F_1)$ and $\#(F_2 \simeq_{\mathrm{alg}[E]} F_2)$ are coprime. Then there exist $m \neq 0$ and a number field $F'$, Galois over $E$ with cyclic group $F' \simeq_{\mathrm{alg}[E]} F'$, such that: there is an $E$-algebra homomorphism $F' \to \mathrm{CyclotomicField}\, m\, E$; every automorphism stabilising an infinite place of $F'$ is the identity; $n_1 n_2 \mid \#(F' \simeq_{\mathrm{alg}[E]} F')$; for every $v \in T$ and every height-one prime $w$ of $\mathcal{O}_{F'}$ under $v$ one has $n_1 n_2 \mid \# D_w$; and $\#(F' \simeq_{\mathrm{alg}[E]} F')$ divides $\#(F_1 \simeq_{\mathrm{alg}[E]} F_1) \cdot \#(F_2 \simeq_{\mathrm{alg}[E]} F_2)$.
--
--   This is the compositum step in Artin's lemma on auxiliary cyclic cyclotomic extensions with prescribed local degrees: two cyclic cyclotomic layers of coprime degree are combined into a single cyclic cyclotomic layer whose global and local degrees absorb both prescribed divisibilities. It is used by [`NumberField.exists_isCyclic_algHom_cyclotomicField_dvd_natCard_decomp`](thm.html#NumberField.exists_isCyclic_algHom_cyclotomicField_dvd_natCard_decomp), where it reduces the statement for a general $n$ to its prime-power case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_exists_isCyclic_algHom_cyclotomicField_mul_dvd_natCard_decomp_of_coprime.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
open NumberField IsDedekindDomain

theorem NumberField.exists_isCyclic_algHom_cyclotomicField_mul_dvd_natCard_decomp_of_coprime
    (E : Type) [Field E] [NumberField E] (T : Finset (HeightOneSpectrum (𝓞 E)))
    (n₁ m₁ : ℕ) [NeZero m₁] (F₁ : Type) [Field F₁] [NumberField F₁] [Algebra E F₁] [IsGalois E F₁]
    [IsCyclic (F₁ ≃ₐ[E] F₁)] (hcyc₁ : Nonempty (F₁ →ₐ[E] CyclotomicField m₁ E))
    (hinf₁ : ∀ (w : InfinitePlace F₁) (g : (F₁ ≃ₐ[E] F₁)), g ∈ NumberField.InfPlaceDecomp.decomp E F₁ w → g = 1)
    (hdeg₁ : n₁ ∣ Nat.card (F₁ ≃ₐ[E] F₁))
    (hloc₁ : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 F₁), w.under (𝓞 E) = v →
      n₁ ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F₁ w))
    (n₂ m₂ : ℕ) [NeZero m₂] (F₂ : Type) [Field F₂] [NumberField F₂] [Algebra E F₂] [IsGalois E F₂]
    [IsCyclic (F₂ ≃ₐ[E] F₂)] (hcyc₂ : Nonempty (F₂ →ₐ[E] CyclotomicField m₂ E))
    (hinf₂ : ∀ (w : InfinitePlace F₂) (g : (F₂ ≃ₐ[E] F₂)), g ∈ NumberField.InfPlaceDecomp.decomp E F₂ w → g = 1)
    (hdeg₂ : n₂ ∣ Nat.card (F₂ ≃ₐ[E] F₂))
    (hloc₂ : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 F₂), w.under (𝓞 E) = v →
      n₂ ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F₂ w))
    (hcop : Nat.Coprime (Nat.card (F₁ ≃ₐ[E] F₁)) (Nat.card (F₂ ≃ₐ[E] F₂))) :
    ∃ (m : ℕ) (_ : NeZero m) (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra E F') (_ : IsGalois E F')
      (_ : IsCyclic (F' ≃ₐ[E] F')),

      Nonempty (F' →ₐ[E] CyclotomicField m E) ∧

      (∀ (w : InfinitePlace F') (g : (F' ≃ₐ[E] F')), g ∈ NumberField.InfPlaceDecomp.decomp E F' w → g = 1) ∧

      n₁ * n₂ ∣ Nat.card (F' ≃ₐ[E] F') ∧

      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 F'), w.under (𝓞 E) = v →
        n₁ * n₂ ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)) ∧

      Nat.card (F' ≃ₐ[E] F') ∣ Nat.card (F₁ ≃ₐ[E] F₁) * Nat.card (F₂ ≃ₐ[E] F₂) := by sorry
