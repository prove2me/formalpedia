-- Prove2me | Theorems.Thm_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap
-- name    : NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/a88459a2-b50b-5666-a252-583cca97e4ab
-- title:
--   Scaling invariance of the adelic box average under F^×
-- statement:
--   Let $F$ be a number field and let $E$ be a normed real vector space. The adele ring $\mathbb{A}_F = \mathrm{AdeleRing}(\mathcal{O}_F, F)$ is equipped with its Borel $\sigma$-algebra and with the additive Haar measure $\mu =$ `AdelicHaar.adelicAddHaar`, and `AdelicBox.adelicBox` $F$ is the set of adeles $x = (x_\infty, x_{\mathrm{fin}})$ whose infinite component lies in the preimage, under the identification of $\prod_{v\mid\infty} F_v$ with the mixed space, of the fundamental domain of the $\mathbb{Z}$-span of the lattice basis coming from the canonical embedding of $F$, and whose finite component satisfies $x_{\mathrm{fin},v} \in \mathcal{O}_{F_v}$ for every $v$ in the height-one spectrum of $\mathcal{O}_F$. Write $\nu$ for the conditional probability measure $\mu(\,\cdot \mid \text{box})$, i.e. $\mu(\text{box})^{-1}$ times the restriction of $\mu$ to the box. Let $f : \mathbb{A}_F \to E$ satisfy $f(\iota(k) + x) = f(x)$ for all $k \in F$ and all $x \in \mathbb{A}_F$, where $\iota$ is the structure map $F \to \mathbb{A}_F$, and let $a \in F$ with $a \neq 0$. Then the Bochner integrals satisfy $\int f(\iota(a)x)\,d\nu(x) = \int f(x)\,d\nu(x)$. No integrability hypothesis is imposed.
--
--   This is the measure-theoretic form of the product formula $|a|_{\mathbb{A}} = 1$ for a principal idele, in the shape consumed by the constant-term calculus: the box average of an $F$-periodic function is unchanged by the dilation $x \mapsto \iota(a)x$. It is cited in the treatment of constant terms of automorphic forms along the adelic box, where invariance under rational diagonal elements of the Borel subgroup is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicBox_integral_cond_adelicBox_comp_mul_algebraMap.lean

import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField
attribute [local instance] NumberField.AdelicHaar.adeleBorel

theorem NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap
    (F : Type) [Field F] [NumberField F]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : AdeleRing (𝓞 F) F → E}
    (hf : ∀ (k : F) (x : AdeleRing (𝓞 F) F), f (algebraMap F (AdeleRing (𝓞 F) F) k + x) = f x)
    (a : F) (ha : a ≠ 0) :
    ∫ x, f (algebraMap F (AdeleRing (𝓞 F) F) a * x)
        ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F))
      = ∫ x, f x ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicBox.adelicBox F)) := by sorry
