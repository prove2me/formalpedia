-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_ne_zero_of_hasProd_inducedEulerPoly_eval_inv
-- name    : LanglandsTunnell.CubicInduction.exists_forall_ne_zero_of_hasProd_inducedEulerPoly_eval_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/bac466fb-3356-547a-b4d4-184c95bf3b0a
-- title:
--   Non-vanishing of the partial twisted induced Euler product
-- statement:
--   Let $K$ be a number field equipped with an $\mathcal O_{\mathbb Q}$-algebra structure on $\mathcal O_K$ that is integral, and assume $[K:\mathbb Q]=3$. Let $\mu$ be a homomorphism from the ideles $(\mathbb A_K)^\times$ to $\mathbb C^\times$ which is an admissible twist, i.e. trivial on the principal ideles coming from $K^\times$, continuous, and of absolute value $1$ at every idele; let $S$ be a finite set of finite places of $\mathbb Q$, and let $\tau$ be an admissible twist of $\mathbb Q$ in the same sense. Then there is a real $\sigma_L$ such that for every $s\in\mathbb C$ with $\operatorname{Re} s>\sigma_L$ and every $L\in\mathbb C$, if the family indexed by the primes $p\notin S$ of $\mathcal O_{\mathbb Q}$ whose $p$-th term is $\bigl(P_p(c_\tau(p)\,N(p)^{-s})\bigr)^{-1}$ is multipliable with product $L$, then $L\neq 0$. Here $N(p)$ is the absolute norm of $p$; $c_\tau(p)=\tau(\varpi_p)$ for a uniformiser idele at $p$ when $\tau$ is unramified at $p$ (its local character is trivial on the units of the completion that are integral together with their inverses) and $c_\tau(p)=0$ otherwise; and $P_p=\prod_{\mathfrak P\mid p}\bigl(1-c_\mu(\mathfrak P)X^{f(\mathfrak P/p)}\bigr)$ is the induced Euler polynomial, the product over the primes $\mathfrak P$ of $\mathcal O_K$ lying under $p$, with $f$ the inertia degree and $c_\mu(\mathfrak P)=\mu(\varpi_{\mathfrak P})$ when $\mu$ is unramified at $\mathfrak P$, $0$ otherwise.
--
--   This is the statement that the partial Euler product of the $\tau$-twisted $L$-function attached by induction to an idele class character of a cubic field is non-zero in a suitable right half-plane, expressed as a uniqueness-free assertion about any value of the unconditionally convergent product. It is the only property of the good factors used in the place-separation step of the cubic-induction construction, where the off-$v$ factor of the global zeta integral must be invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_ne_zero_of_hasProd_inducedEulerPoly_eval_inv.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse
  LanglandsTunnell.CubicInduction LanglandsTunnell.TateLocal MeasureTheory LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicInduction.exists_forall_ne_zero_of_hasProd_inducedEulerPoly_eval_inv
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (_hτ : IsAdmissibleTwist ℚ τ) :
    ∃ σL : ℝ, ∀ s : ℂ, σL < s.re → ∀ L : ℂ,
      HasProd (fun p : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ S} =>
          ((inducedEulerPoly ℚ (inducedCoeff K μ) p.1).eval
            (LanglandsTunnell.CubicLambda.eulerCoeff ℚ τ p.1 * (Ideal.absNorm p.1.asIdeal : ℂ) ^ (-s)))⁻¹) L →
      L ≠ 0 := by sorry
