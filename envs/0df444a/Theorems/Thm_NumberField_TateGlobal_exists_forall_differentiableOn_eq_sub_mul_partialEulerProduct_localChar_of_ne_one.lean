-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_forall_differentiableOn_eq_sub_mul_partialEulerProduct_localChar_of_ne_one
-- name    : NumberField.TateGlobal.exists_forall_differentiableOn_eq_sub_mul_partialEulerProduct_localChar_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/a1a92fcd-fd6d-53f1-bf03-8ecf8d7d4aed
-- title:
--   Partial Hecke L-function of a nontrivial unitary idele class character on Re w>0
-- statement:
--   Let $F$ be a number field and let $\chi \colon \mathbb{A}_F^\times \to \mathbb{C}^\times$ be a group homomorphism on the units of the adele ring of $F$ which is continuous, unitary in the sense that $\lVert \chi(x)\rVert = 1$ for every idele unit $x$ (`IsUnitaryChar`), trivial on the image of $F^\times$ under the diagonal embedding, i.e. $\chi(\iota(u)) = 1$ for all $u \in F^\times$ (`IsIdeleClassChar`), and not the trivial character. Then there exists $s_1 \in \mathbb{C}$ with $\operatorname{Re} s_1 = 1$ and $s_1 \neq 1$ — depending on $\chi$ alone — such that for every finite set $S$ of height-one primes of $\mathcal{O}_F$ and every family $(\varpi_v)_v$ of units $\varpi_v \in (F_v)^\times$ indexed by the height-one primes with $v(\varpi_v) = \mathrm{ofAdd}(-1)$, i.e. each $\varpi_v$ a uniformiser, there is a function $Q \colon \mathbb{C} \to \mathbb{C}$ differentiable on the half-plane $\{\operatorname{Re} w > 0\}$ satisfying, for every $w$ with $\operatorname{Re} w > 1$, $$Q(w) = (w - s_1)\Bigl(\prod_{v \notin S} \bigl(1 - \chi_v(\varpi_v)\,N(v)^{-w}\bigr)\Bigr)^{-1},$$ the inverse being taken of the whole infinite product; here $N(v) = \lvert \mathcal{O}_F/v \rvert$ is the absolute norm and $\chi_v =$ `localChar` $\chi\,v$ is the character of $(F_v)^\times$ obtained by sending $t$ to the idele unit that is $t$ at $v$ and $1$ at every other finite place and at the infinite places, and applying $\chi$.
--
--   This is the analytic continuation, in Tate's form, of the partial Hecke $L$-function $L^S(w,\chi) = \prod_{v \notin S}(1 - \chi_v(\varpi_v)N(v)^{-w})^{-1}$ of a nontrivial unitary idele class character to the half-plane $\operatorname{Re} w > 0$, packaged so that the only possible pole is cleared by a single linear factor $w - s_1$ chosen once for $\chi$ (the two cases being $\chi$ nontrivial on the norm-one ideles, where $L^S$ is entire, and $\chi = \lVert\cdot\rVert^{it}$ with $t \neq 0$, where the pole sits at $1 - it$). It feeds the meromorphic continuation of Weyl intertwining integrals of induced sections in the adelic automorphic theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_forall_differentiableOn_eq_sub_mul_partialEulerProduct_localChar_of_ne_one.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain

theorem NumberField.TateGlobal.exists_forall_differentiableOn_eq_sub_mul_partialEulerProduct_localChar_of_ne_one
    (F : Type) [Field F] [NumberField F]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ) (hχ1 : χ ≠ 1) :
    ∃ s₁ : ℂ, s₁.re = 1 ∧ s₁ ≠ 1 ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 F)))
        (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
        (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)),
        ∃ Q : ℂ → ℂ, DifferentiableOn ℂ Q {w : ℂ | 0 < w.re} ∧
          ∀ w : ℂ, 1 < w.re →
            Q w = (w - s₁) * (∏' v : {v // v ∉ S},
              (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ := by sorry
