-- Prove2me | Theorems.Thm_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles
-- name    : NumberField.AdelicBox.exists_eq_sum_indicator_pi_image_integralFiniteAdeles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/63222ba9-692d-55c7-b9ee-081d7c24c364
-- title:
--   Box-indicator decomposition of Schwartz–Bruhat functions on finite adeles
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and finite adele ring $\mathbb{A}_{F,f} =$ `FiniteAdeleRing (𝓞 F) F`, and let $\iota$ be a finite index type. Let $h\colon (\iota \to \mathbb{A}_{F,f}) \to \mathbb{C}$ be a function on the $\iota$-fold power of the finite adele ring which is locally constant and has compact support. Then there exist a nonzero $d \in \mathcal{O}_F$, a finite set $s$ of vectors $k \in \iota \to F$, and a function $c$ on $\iota \to F$ with complex values, such that $h$ equals $\sum_{k \in s} c_k \cdot \mathbf{1}_{B_k}$, where $\mathbf{1}_{B_k}$ is the indicator (with value the constant function $1$) of the box $B_k = \prod_{i \in \iota} \bigl(k_i + d\,\widehat{\mathcal{O}}\bigr)$; here each side is the image of $\widehat{\mathcal{O}} = \{x \in \mathbb{A}_{F,f} : x_v \in \mathcal{O}_v \text{ for every height-one prime } v \text{ of } \mathcal{O}_F\}$ under $z \mapsto k_i + d z$ (images taken along the structure map $F \to \mathbb{A}_{F,f}$), and the product over $i$ is formed as a `Set.pi` over the whole index type. The modulus $d$ is the same for all $k$ and all coordinates $i$.
--
--   This is the several-variable structure theorem for the Schwartz–Bruhat space of the finite adeles: a locally constant compactly supported function on $\mathbb{A}_{F,f}^{\iota}$ is a finite linear combination of indicators of boxes whose sides are cosets $k_i + d\widehat{\mathcal{O}}$ with a common modulus $d \in \mathcal{O}_F \setminus \{0\}$. It is deduced from the one-variable case [`NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles`](thm.html#NumberField.AdelicBox.exists_eq_sum_indicator_image_integralFiniteAdeles), and is used in the adelic Fourier analysis feeding the Poisson summation formula and the Schwartz–Bruhat estimates for the adelic Fourier transform.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicBox_exists_eq_sum_indicator_pi_image_integralFiniteAdeles.lean

import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicBox IsDedekindDomain

theorem NumberField.AdelicBox.exists_eq_sum_indicator_pi_image_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    {h : (ι → FiniteAdeleRing (𝓞 F) F) → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ (s : Finset (ι → F)) (c : (ι → F) → ℂ),
      h = ∑ k ∈ s, c k •
        (Set.pi Set.univ fun i => (fun z : FiniteAdeleRing (𝓞 F) F ↦
            algebraMap F (FiniteAdeleRing (𝓞 F) F) (k i)
              + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1 := by sorry
