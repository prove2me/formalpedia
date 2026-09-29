-- Prove2me | Theorems.Thm_NumberField_TateGlobal_exists_one_le_mul_norm_of_eq_sub_mul_partialEulerProduct_normPowChar
-- name    : NumberField.TateGlobal.exists_one_le_mul_norm_of_eq_sub_mul_partialEulerProduct_normPowChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/cc565777-b225-51c1-ba4b-400dccc2fe30
-- title:
--   Polynomial lower bound for regularised shifted partial Dedekind zeta
-- statement:
--   Let $K$ be a number field, $\tau$ a real number and $T$ a finite set of maximal ideals of $\mathcal{O}_K$. Let $Q\colon\mathbb{C}\to\mathbb{C}$ be entire and assume that for every $s$ with $\operatorname{Re} s>1$ one has $Q(s)=(s-(1-i\tau))\cdot\prod'_{v\notin T}\bigl(1-c_v\,N(v)^{-s}\bigr)^{-1}$, the product being taken over the maximal ideals $v$ of $\mathcal{O}_K$ outside $T$, with $N(v)=\mathrm{absNorm}(v)$ the absolute norm of $v$, and with $c_v$ defined as the value of the character $\mathrm{normPowChar}\,K\,\tau$ — the homomorphism on the ideles sending a unit $x$ to $\lVert x\rVert^{i\tau}$, where $\lVert x\rVert$ is the module of $x$ for the Haar measure of the adele ring — at the idele that is $1$ at every place except $v$ and is a uniformiser at $v$, provided that character is unramified at $v$ in the sense that it is trivial on all local units $t$ at $v$ with $t$ and $t^{-1}$ both in the valuation ring, and $c_v=0$ otherwise (by a cited identity $c_v=N(v)^{-i\tau}$ always). The conclusion is that there exist a real number $A$ and a natural number $N$ such that $1\le A\,(1+|\operatorname{Im} w|)^N\,\lVert Q(w)\rVert$ for every $w$ with $\operatorname{Re} w\ge 1$.
--
--   This is the classical lower bound coming from the zero-free region of the Dedekind zeta function on the closed half-plane $\operatorname{Re} w\ge 1$ (Hadamard–de la Vallée Poussin, Landau), applied to $\zeta_{K,T}(w+i\tau)$ after removal of the pole at $w=1-i\tau$: in particular $Q$ has no zero there, and $1/Q$ grows at most polynomially in $|\operatorname{Im} w|$. It is used in the analytic continuation and polynomial-growth estimates for regularised intertwining integrals attached to induced sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_exists_one_le_mul_norm_of_eq_sub_mul_partialEulerProduct_normPowChar.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal
open scoped Classical in

theorem NumberField.TateGlobal.exists_one_le_mul_norm_of_eq_sub_mul_partialEulerProduct_normPowChar
    (K : Type) [Field K] [NumberField K] (τ : ℝ) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (Q : ℂ → ℂ) (_hQ : Differentiable ℂ Q)
    (_hQE : ∀ s : ℂ, 1 < s.re →
      Q s = (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt (normPowChar K τ) v.1 then
                (((normPowChar K τ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, 1 ≤ w.re →
      1 ≤ A * (1 + |w.im|) ^ N * ‖Q w‖ := by sorry
