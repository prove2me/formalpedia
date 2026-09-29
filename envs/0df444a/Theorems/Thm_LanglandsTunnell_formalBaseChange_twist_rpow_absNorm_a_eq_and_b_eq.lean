-- Prove2me | Theorems.Thm_LanglandsTunnell_formalBaseChange_twist_rpow_absNorm_a_eq_and_b_eq
-- name    : LanglandsTunnell.formalBaseChange_twist_rpow_absNorm_a_eq_and_b_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/8dffd854-c3f0-5e6e-b9ff-f9e40f62f3c9
-- title:
--   Formal base change commutes with norm twists, primewise
-- statement:
--   Let $F$ and $K$ be number fields together with an algebra structure on $\mathcal{O}_K$ over $\mathcal{O}_F$ that is integral, let $\Phi$ be a Hecke eigensystem over $F$ with values in $\mathbb{C}$ — that is, a nonzero level ideal of $\mathcal{O}_F$ and two functions $a,b$ from the height one spectrum of $\mathcal{O}_F$ to $\mathbb{C}$ — let $t\in\mathbb{R}$, and let $\mathfrak{P}$ be a height one prime of $\mathcal{O}_K$, lying under the prime $\mathfrak{p}=\mathfrak{P}\cap\mathcal{O}_F$ with residual degree $f=\mathrm{inertiaDeg}'(\mathfrak{p},\mathfrak{P})$. Here `twist` by a function $\chi$ multiplies $a$ by $\chi$ and $b$ by $\chi^2$ and keeps the level, while `formalBaseChange` sends a system $\pi$ over $F$ to the system over $K$ of level $\top$ with $a(\mathfrak{P})=\mathrm{satakePow}_f(\pi.a(\mathfrak{p}),\pi.b(\mathfrak{p}))$ and $b(\mathfrak{P})=\pi.b(\mathfrak{p})^{f}$, where $\mathrm{satakePow}$ is defined by $\mathrm{satakePow}_0=2$, $\mathrm{satakePow}_1(s,e)=s$ and $\mathrm{satakePow}_{n+2}=s\,\mathrm{satakePow}_{n+1}-e\,\mathrm{satakePow}_n$. The assertion is the conjunction of two equalities at the single prime $\mathfrak{P}$: the $a$-entry and the $b$-entry of the formal base change of $\Phi$ twisted by $v\mapsto (\mathrm{N}v)^{-t}$ on primes of $F$ agree with the $a$-entry and $b$-entry of the twist by $v\mapsto (\mathrm{N}v)^{-t}$ on primes of $K$ of the formal base change of $\Phi$, the norms being absolute ideal norms raised to the real power $-t$ and cast into $\mathbb{C}$.
--
--   The statement records that the formal base-change operation on Hecke eigensystem data is compatible with twisting by a power of the absolute norm, at every prime rather than merely away from a finite set. It is used in the Langlands–Tunnell part of the development, where such an identity is needed at all primes outside a controlled set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_formalBaseChange_twist_rpow_absNorm_a_eq_and_b_eq.lean

import Definitions.Def_AutomorphicForm_FormalBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem LanglandsTunnell.formalBaseChange_twist_rpow_absNorm_a_eq_and_b_eq
    (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
    (Φ : HeckeEigensystem F ℂ) (t : ℝ) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange F K (Φ.twist (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))).a 𝔓 =
      ((formalBaseChange F K Φ).twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).a 𝔓 ∧
    (formalBaseChange F K (Φ.twist (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))).b 𝔓 =
      ((formalBaseChange F K Φ).twist (fun v : HeightOneSpectrum (𝓞 K) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ))).b 𝔓 := by sorry
