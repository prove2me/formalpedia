-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two
-- name    : LanglandsTunnell.TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/24fd3923-4e0b-5126-bc49-b4b938d71d3a
-- title:
--   Root number under composition with an unramified quadratic norm
-- statement:
--   Let $E$ and $M$ be number fields with $M$ an $E$-algebra, let $v$ be a height-one prime of $\mathcal O_E$ and let $w$ be an extension of $v$ to $\mathcal O_M$, i.e. a height-one prime of $\mathcal O_M$ whose contraction to $\mathcal O_E$ is $v$. Assume the ramification index of $w$ over $v$ is $1$ and the inertia degree is $2$. Let $\mu : (E_v)^\times \to \mathbb C^\times$ be a group homomorphism from the units of the $v$-adic completion $E_v$, and let $a$ be a natural number such that $\mu$ has conductor exponent $a$ at $v$: $\mu$ is trivial on the set of units $u$ with $|u| = 1$ and (if $a \neq 0$) $|u-1| \le q_v^{-a}$, while for every $m < a$ there is a unit in the corresponding set at level $m$ on which $\mu$ is non-trivial. Assume further that $|\mu(\varpi_v)| = 1$, where $\varpi_v$ is the image in $E_v$ of the chosen uniformizer of $v$. Then the character $\mu \circ N_{M_w/E_v}$ of $(M_w)^\times$, obtained by composing $\mu$ with the units map induced by the algebra norm of $M_w$ over $E_v$, again has conductor exponent $a$ at $w$, and its standard local root number (Tate's local $\varepsilon$-factor at $s = 1/2$, formed with the self-dual Haar measure, the local standard additive character $\psi_{M,w}$ and the standard test function) satisfies $\varepsilon(\mu \circ N_{M_w/E_v}) = (-1)^a\,\varepsilon(\mu)^2$.
--
--   This is the local computation of the $\varepsilon$-factor of a character of a local field composed with the norm from its unramified quadratic extension, in the normalisation of Tate's local functional equation; the resulting sign $(-1)^a$ is the standard discrepancy between $\varepsilon$ of the induced (or base-changed) datum and the square of $\varepsilon(\mu)$. It feeds the cubic-induction step of the Langlands–Tunnell argument, where global root numbers are compared place by place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem LanglandsTunnell.TateLocal.stdRootNumberAt_comp_norm_of_inertiaDeg_eq_two
    (E M : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (he : v.asIdeal.ramificationIdx' w.1.asIdeal = 1)
    (hf : v.asIdeal.inertiaDeg' w.1.asIdeal = 2)
    (μ : (v.adicCompletion E)ˣ →* ℂˣ) (a : ℕ) (ha : HasConductorExponentAt E v μ a)
    (hμ : ‖(μ (uniformizerUnit E v) : ℂ)‖ = 1) :
    HasConductorExponentAt M w.1
        (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) a ∧
      stdRootNumberAt M w.1
          (μ.comp (Units.map (Algebra.norm (v.adicCompletion E)))) =
        (-1) ^ a * stdRootNumberAt E v μ ^ 2 := by sorry
