-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq
-- name    : LanglandsTunnell.TateLocal.isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/a46178d9-66a2-5425-a3e9-f47543a5b688
-- title:
--   Fourier inversion on ℚₚ × ℚₚ for Schwartz–Bruhat functions
-- statement:
--   Let $p$ be a point of the height one spectrum of the ring of integers of $\mathbb{Q}$, let $F = \mathbb{Q}_p$ denote the completion `p.adicCompletion ℚ`, and let $f : F \times F \to \mathbb{C}$ satisfy `IsSchwartzBruhat f`, i.e. $f$ is locally constant and has compact support. Equip $F$ with the Borel $\sigma$-algebra `localBorel ℚ p` and with the measure `selfDualHaarAt ℚ p`, the additive Haar measure normalised by the factor $N(p)^{-n/2}$, where $N(p)$ is the absolute norm of the prime and $n$ is the level `addCharLevel` of the character `psiLocal ℚ p` obtained by composing the standard adelic additive character of $\mathbb{Q}$ with the additive embedding of $F$ into the adele ring at the place $p$; equip $F \times F$ with the corresponding product measure. Writing $\psi =$ `psiLocal ℚ p`, the conclusion is the conjunction of two assertions: first, the transform $y \mapsto \int_{F \times F} f(x)\,\psi(x_1 y_1 + x_2 y_2)\,dx$ is again locally constant with compact support; second, for every $x \in F \times F$, applying this transform twice returns $f(-x)$, where the inner transform is integrated against the same product measure and paired with $\psi(y_1x_1 + y_2x_2)$.
--
--   This is the two-variable form of Tate's local Fourier inversion theorem at a finite place, for the self-dual normalisation of Haar measure, in which the inversion constant is $1$ and double transformation is precisely composition with $x \mapsto -x$. It is used for the local theory of $2 \times 2$ matrix Fourier transforms and for the local Rankin–Selberg integrals attached to principal series, where functional equations are obtained by passing to the dual function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal

theorem LanglandsTunnell.TateLocal.isSchwartzBruhat_prodFourier_and_prodFourier_prodFourier_selfDualHaarAt_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (f : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hf : IsSchwartzBruhat f) :
    letI := localBorel ℚ p
    IsSchwartzBruhat (fun y : p.adicCompletion ℚ × p.adicCompletion ℚ =>
        ∫ x : p.adicCompletion ℚ × p.adicCompletion ℚ,
          f x * psiLocal ℚ p (x.1 * y.1 + x.2 * y.2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) ∧
      ∀ x : p.adicCompletion ℚ × p.adicCompletion ℚ,
        (∫ y : p.adicCompletion ℚ × p.adicCompletion ℚ,
            (∫ z : p.adicCompletion ℚ × p.adicCompletion ℚ,
                f z * psiLocal ℚ p (z.1 * y.1 + z.2 * y.2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) *
              psiLocal ℚ p (y.1 * x.1 + y.2 * x.2) ∂((selfDualHaarAt ℚ p).prod (selfDualHaarAt ℚ p))) =
          f (-x) := by sorry
