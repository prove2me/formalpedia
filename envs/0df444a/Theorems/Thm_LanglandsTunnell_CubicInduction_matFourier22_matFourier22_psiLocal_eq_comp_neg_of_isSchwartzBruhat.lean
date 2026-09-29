-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_matFourier22_matFourier22_psiLocal_eq_comp_neg_of_isSchwartzBruhat
-- name    : LanglandsTunnell.CubicInduction.matFourier22_matFourier22_psiLocal_eq_comp_neg_of_isSchwartzBruhat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/551e8b0b-f458-5688-bb83-2a386c058611
-- title:
--   Fourier inversion for `matFourier22` on M₂(ℚₚ)
-- statement:
--   Let $p$ be a finite place of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and write $F = \mathbb{Q}_p$ for the completion `p.adicCompletion ℚ`. Let $\Phi : M_2(F) \to \mathbb{C}$ be Schwartz–Bruhat, meaning (by the definition of `IsSchwartzBruhat`) that $\Phi$ is locally constant and has compact support. The additive character used throughout is [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65), the composite of the standard additive character of the adele ring of $\mathbb{Q}$ with the additive map placing an element of $F$ in the component at $p$ and $0$ elsewhere. For a character $\eta$ and an index $j$, `colFourier22 p η j φ` sends $X$ to $\int_{F\times F} \varphi(\text{$X$ with column $j$ replaced by $u$})\,\eta(u_1 X_{0j} + u_2 X_{1j})$, the integral taken against the product of two copies of the self-dual Haar measure `selfDualHaarAt ℚ p`; and `matFourier22 p η` is `colFourier22 p η 0` applied to `colFourier22 p η 1`. The assertion is that applying `matFourier22 p (psiLocal ℚ p)` twice to $\Phi$ yields, as a function on $M_2(F)$, the map $X \mapsto \Phi(-X)$, an equality of functions on the nose.
--
--   This is Fourier inversion on $M_2(\mathbb{Q}_p) \cong \mathbb{Q}_p^4$ for the trace pairing, with constant exactly $1$ because the Haar measure is self-dual for the standard character and both transforms use the same kernel, so the second application evaluates at $-X$. It is used in the local theory of Rankin–Selberg integrals for $\mathrm{GL}_2$, in the functional-equation arguments for local integrals attached to principal series and to cuspidal representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_matFourier22_matFourier22_psiLocal_eq_comp_neg_of_isSchwartzBruhat.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.TateLocal
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.matFourier22_matFourier22_psiLocal_eq_comp_neg_of_isSchwartzBruhat
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Φ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) → ℂ) (hΦ : IsSchwartzBruhat Φ) :
    matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p)
        (matFourier22 p (NumberField.StandardAddChar.psiLocal ℚ p) Φ) =
      fun X : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ) => Φ (-X) := by sorry
