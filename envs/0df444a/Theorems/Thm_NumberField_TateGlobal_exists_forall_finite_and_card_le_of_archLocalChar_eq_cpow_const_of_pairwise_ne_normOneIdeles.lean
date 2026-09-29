-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_forall_finite_and_card_le_of_archLocalChar_eq_cpow_const_of_pairwise_ne_normOneIdeles
-- name    : NumberField.TateGlobal.exists_forall_finite_and_card_le_of_archLocalChar_eq_cpow_const_of_pairwise_ne_normOneIdeles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/82b038b8-e83c-51b0-94b9-62e8496491ca
-- title:
--   Uniform finiteness bound for unramified idele class characters
-- statement:
--   Let $K$ be a number field. The assertion is that there is a natural number $N$, depending only on $K$, with the following property. Let $\iota$ be any type, let $\chi : \iota \to ((\mathbb{A}_K)^\times \to \mathbb{C}^\times)$ be a family of group homomorphisms from the units of the adele ring `AdeleRing (𝓞 K) K` to $\mathbb{C}^\times$, and let $\sigma_0 : \iota \to \mathbb{R}$. Assume: (i) for each $i$ the map $z \mapsto \chi_i(z)$ is continuous as a map into $\mathbb{C}$; (ii) each $\chi_i$ is an idele class character in the sense of `IsIdeleClassChar`, i.e. $\chi_i$ kills the image of $K^\times$ under the map induced by $K \to \mathbb{A}_K$; (iii) each $\chi_i$ satisfies `IsUnramifiedCharAt` at every finite place $v$ of $K$, i.e. whenever $t \in (K_v)^\times$ has both $t$ and $t^{-1}$ in the valuation ring $\mathcal{O}_v$, the local character $\chi_i \circ (\text{inclusion of } (K_v)^\times \text{ into the finite idele units})$ sends $t$ to $1$; (iv) for each $i$, each infinite place $v$ and each $x \in (K_v)^\times$, the value of $\chi_i$ on the idele `archUnitHom v x` that is $x$ in the $v$-component of the infinite part and $1$ in all other infinite components and in the finite part equals $(\,\|{\cdot}\|\,)^{\sigma_0(i)\,\mathrm{i}}$, where the base is the real number `ideleNorm K (archUnitHom v x)`, the scaling factor `distribHaarChar` of the adele ring at that idele, and the exponent $\sigma_0(i)\cdot \mathrm{i}$ is purely imaginary and independent of $v$; (v) for $i \neq j$ there exists $z$ in `normOneIdeles K`, the kernel of `distribHaarChar` on $(\mathbb{A}_K)^\times$, with $\chi_i(z) \neq \chi_j(z)$. Then $\iota$ is finite and $\operatorname{card}(\iota) \le N$.
--
--   This is a class-fibre finiteness statement: after the purely imaginary archimedean exponent is normalised away, a level-one idele class character is trivial on $K^\times$, on the archimedean units and on all local integral units, hence factors through a finite quotient of the norm-one idele class group, so characters that are pairwise distinct on the norm-one ideles form a set bounded in size by a constant depending only on $K$. It is used in the automorphic-forms layer, in [`AutomorphicForm.exists_forall_finite_and_ncard_archParam_spread_le_of_isUnitaryChar_of_pairwise_ne_normOneIdeles`](thm.html#AutomorphicForm.exists_forall_finite_and_ncard_archParam_spread_le_of_isUnitaryChar_of_pairwise_ne_normOneIdeles), to bound families of central characters with prescribed archimedean parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_forall_finite_and_card_le_of_archLocalChar_eq_cpow_const_of_pairwise_ne_normOneIdeles.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

theorem NumberField.TateGlobal.exists_forall_finite_and_card_le_of_archLocalChar_eq_cpow_const_of_pairwise_ne_normOneIdeles
    (K : Type) [Field K] [NumberField K] :
    ∃ N : ℕ, ∀ (ι : Type) (χ : ι → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ)) (σ₀ : ι → ℝ),
      (∀ i, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ i z : ℂˣ) : ℂ)) →
      (∀ i, IsIdeleClassChar (𝓞 K) K (χ i)) →
      (∀ i (v : HeightOneSpectrum (𝓞 K)), NumberField.TateGlobal.IsUnramifiedCharAt (χ i) v) →
      (∀ i (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ((NumberField.TateGlobal.archLocalChar (χ i) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((σ₀ i : ℝ) : ℂ) * Complex.I)) →
      (∀ i j, i ≠ j → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K, χ i z ≠ χ j z) →
      Finite ι ∧ Nat.card ι ≤ N := by sorry
