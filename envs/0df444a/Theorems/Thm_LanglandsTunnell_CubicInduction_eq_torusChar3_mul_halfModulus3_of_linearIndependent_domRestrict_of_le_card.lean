-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eq_torusChar3_mul_halfModulus3_of_linearIndependent_domRestrict_of_le_card
-- name    : LanglandsTunnell.CubicInduction.eq_torusChar3_mul_halfModulus3_of_linearIndependent_domRestrict_of_le_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/9ccad917-c81e-555b-a85a-8e6193d9e168
-- title:
--   Equivariant functionals on Bruhat steps of a GL₃ principal series
-- statement:
--   Let $v$ be a finite place of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), let $\chi = (\chi_0,\chi_1,\chi_2)$ be a triple of multiplicative characters $(\mathbb{Q}_v)^\times \to \mathbb{C}^\times$, and let `principalSeries3 v χ` be the space of locally constant $f : \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ with $f(ug)=f(g)$ for every upper unipotent $u = \begin{pmatrix}1&x&z\\0&1&y\\0&0&1\end{pmatrix}$ and $f(\mathrm{diag}(a)g) = \big(\prod_i \chi_i(a_i)\big)\,(\|a_0\|/\|a_2\|)\, f(g)$. Assume $Z : \mathrm{Fin}\,7 \to$ subsets of $\mathrm{GL}_3(\mathbb{Q}_v)$ is the increasing list $\emptyset$; $\{g_{20}=g_{10}=g_{21}=0\}$; $\{g_{20}=g_{21}=0\}$; $\{g_{20}=0,\ g_{10}g_{21}=0\}$; $\{g_{20}=0\}$; $\{g_{20}(g_{10}g_{21}-g_{11}g_{20})=0\}$; the whole group; and that $W_k$ is the subspace of the principal series consisting of the $f$ vanishing at every point of $Z_k$. Let $\theta$ be a complex-valued function on $((\mathbb{Q}_v)^\times)^3$, let $i \in \mathrm{Fin}\,6$, and let $\Lambda_0,\dots,\Lambda_{n-1}$ be linear functionals on the principal series such that each $\Lambda_j$ is invariant under right translation by all upper unipotent matrices, satisfies $\Lambda_j(f(\cdot\,\mathrm{diag}(a))) = \theta(a)\Lambda_j(f)$, vanishes on $W_{i+1}$, and such that the restrictions of the $\Lambda_j$ to $W_i$ are linearly independent over $\mathbb{C}$. If $n \ge 1$, then for all $a$, $\theta(a) = \prod_i \chi_{\sigma(i)}(a_i) \cdot (\|a_0\|/\|a_2\|)$, where $\sigma$ is the $i$-th member of the list $1$, $(0\,1)$, $(1\,2)$, `finRotate 3`, `finRotate 3`$^{-1}$, $(0\,2)$ of permutations of $\mathrm{Fin}\,3$.
--
--   This is the standard computation of the torus action on the Jacquet-type (upper unipotent invariant) functionals supported on a single Bruhat stratum of a $\mathrm{GL}_3$ principal series: on the $i$-th graded piece of the filtration by vanishing on closed unions of Bruhat cells, the diagonal torus acts through the corresponding Weyl permutation of the inducing characters times the half-modulus factor $\|a_0\|/\|a_2\|$. It is used in [`LanglandsTunnell.CubicInduction.card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3`](thm.html#LanglandsTunnell.CubicInduction.card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3) to bound the number of independent such functionals by the number of admissible permutations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eq_torusChar3_mul_halfModulus3_of_linearIndependent_domRestrict_of_le_card.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem
    LanglandsTunnell.CubicInduction.eq_torusChar3_mul_halfModulus3_of_linearIndependent_domRestrict_of_le_card
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Z : Fin 7 → Set (LocalGL3 v))
    (hZ : Z = ![∅,
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 = 0 ∧ gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0},
      {g | cornerEntry v g * lowerMinor v g = 0},
      Set.univ])
    (W : Fin 7 → Submodule ℂ ↥(principalSeries3 v χ))
    (hW : ∀ k : Fin 7, W k = Submodule.comap (principalSeries3 v χ).subtype
      (⨅ g ∈ Z k, LinearMap.ker (LinearMap.proj g : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ)))
    (θ : (Fin 3 → (v.adicCompletion ℚ)ˣ) → ℂ) (i : Fin 6) (n : ℕ)
    (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) :
    (∀ j, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
      Λ j ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ j f) →
    (∀ j, ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (f : ↥(principalSeries3 v χ)),
      Λ j ⟨gl3AmbientRightTranslate (R := ℂ) (diagonal3 v a) f,
          rightTranslate_mem_principalSeries3 f.2 (diagonal3 v a)⟩ = θ a * Λ j f) →
    (∀ j, ∀ f ∈ W i.succ, Λ j f = 0) →
    LinearIndependent ℂ (fun j => (Λ j).domRestrict (W i.castSucc)) →
    1 ≤ n → ∀ a : Fin 3 → (v.adicCompletion ℚ)ˣ,
      θ a = torusChar3 v (χ ∘ ⇑(![1, Equiv.swap 0 1, Equiv.swap 1 2, finRotate 3, (finRotate 3)⁻¹,
        Equiv.swap 0 2] i : Equiv.Perm (Fin 3))) a * halfModulus3 v a := by sorry
