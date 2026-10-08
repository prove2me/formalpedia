-- Prove2me | Theorems.Thm_FoundationsRL_Structured_igw_minimizes_dec_v2
-- name    : FoundationsRL.Structured.igw_minimizes_dec_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:36.330242+00:00
-- url     : https://prove2.me/theorems/f4ddd196-7732-4f87-880c-c315462046c9
-- title:
--   Proposition 14 — IGW minimizes the DEC (v2: $\mathrm{IGW}_{2\gamma}$ in the convention of Eq. (3.36); min–max game in $\overline{\mathbb R}$)
-- statement:
--   This is **Proposition 14** of Foster & Rakhlin (arXiv:2312.16730v1, p. 67) for the multi-armed bandit setting $\Pi=[A]$, $F=\mathbb R^A$, in corrected transcription.
--
--   Let $\hat f\in\mathbb R^A$, $\gamma>0$, and let $\pi_f\in\arg\max_\pi f(\pi)$ denote a fixed maximizer selector. The Inverse Gap Weighting distribution of Definition 4 / Eq. (3.36) with parameter $\eta$ is $p(\pi)=1/(\lambda+2\eta(\hat f(\hat\pi)-\hat f(\pi)))$, where $\hat\pi=\arg\max_\pi\hat f(\pi)$ and $\lambda\in[1,A]$ is chosen so that $\sum_\pi p(\pi)=1$ (`IsIGW`). Let $p=\mathrm{IGW}_{2\gamma}(\hat f)$, i.e. $p(\pi)=1/(\lambda+4\gamma(\hat f(\hat\pi)-\hat f(\pi)))$. For $q\in\Delta([A])$ write
--   $$G(q)=\sup_{f\in\mathbb R^A}\ \mathbb E_{\pi\sim q}\big[f(\pi_f)-f(\pi)-\gamma(f(\pi)-\hat f(\pi))^2\big]\in\overline{\mathbb R},$$
--   so that $\mathrm{dec}_\gamma(F,\hat f)=\inf_{q\in\Delta([A])}G(q)$ (Eq. (4.15)). Then
--   $$G(p)=\frac{A-1}{4\gamma}\qquad\text{and}\qquad\inf_{q\in\Delta([A])}G(q)=\frac{A-1}{4\gamma},$$
--   so $p$ is an exact minimizer of the min–max game and certifies $\mathrm{dec}_\gamma(F,\hat f)=(A-1)/(4\gamma)$.
--
--   **Formalization Note.** The printed proposition names $\mathrm{IGW}_{4\gamma}$, a leftover from the convention without the factor $2$ in the denominator; with the book's own Eq. (3.36), the equalizing identity (4.21), $1/(4\gamma p(\pi^\star))=\lambda/(4\gamma)+\hat f(\hat\pi)-\hat f(\pi^\star)$, holds exactly for $\mathrm{IGW}_{2\gamma}$, and the accepted disproof exhibits an $\mathrm{IGW}_{4\gamma}$ distribution whose game value is not $(A-1)/(4\gamma)$; the retired statement had transcribed the printed parameter. The new statement uses $\mathrm{IGW}_{2\gamma}$ and states exactly the printed claim (exact minimizer, value $(A-1)/(4\gamma)$). The suprema and the infimum are taken in the extended reals $\overline{\mathbb R}$ (`EReal`): for a $q$ putting zero weight on some arm the inner supremum over the unbounded class $\mathbb R^A$ is genuinely $+\infty$, which is represented faithfully, whereas the platform's real-valued `decGf` returns Lean's junk value $0$ there — this made the retired version's conjunct "`decGf` $\le(A-1)/(4\gamma)$" true only through the junk value, so `decGf` is not used. A fixed maximizer selector $\pi_f$ is supplied for every $f$ (the payoff does not depend on which maximizer is chosen). $A=0$ is excluded by the existence of the greedy arm; for $A=1$ both sides are $0$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 67, Proposition 14, and Definition 4 / Eq. (3.36) (p. 50), Eq. (4.15) (p. 65) — corrected transcription of the IGW parameter: IGW_{2γ} (the printed IGW_{4γ} is inconsistent with Eq. (3.36) and with the equalizing identity (4.21))

import Mathlib
import Definitions.Def_FoundationsRL_Structured_DEC
import Definitions.Def_FoundationsRL_Contextual_IsIGW

namespace FoundationsRL.Structured

/-- **Proposition 14** (IGW minimizes the DEC) (Foster & Rakhlin, arXiv:2312.16730v1, p. 67),
corrected transcription: for the multi-armed bandit setting `Π = [A]`, `F = ℝ^A`, the Inverse
Gap Weighting distribution `p = IGW_{2γ}(f̂)` of Definition 4 / Eq. (3.36), i.e.
`p(π) = 1/(λ + 4γ(f̂(π̂) − f̂(π)))` with `λ ∈ [1, A]`, is an exact minimizer of the min–max game
`inf_{q ∈ Δ(Π)} sup_{f ∈ ℝ^A} E_{π∼q}[f(π_f) − f(π) − γ (f(π) − f̂(π))²]` defining `dec_γ(F, f̂)`
(Eq. (4.15)), and certifies that its value is `(A − 1)/(4γ)`: the first conjunct says the inner
supremum at `p` equals `(A − 1)/(4γ)`, the second that the infimum over the whole simplex of
the inner suprema equals the same number, so `p` attains the infimum. Both the suprema and the
infimum are taken in `EReal`, where a supremum over the unbounded class `ℝ^A` (which is `+∞`
for any `q` that puts zero weight on some arm) is represented faithfully.

Corrected replacement of `igw_minimizes_dec`: the printed proposition says `IGW_{4γ}`, a
leftover from the convention without the factor `2` in (3.36); with the book's own (3.36) the
equalizing identity (4.21) holds for `IGW_{2γ}` only (the disproof exhibits `IGW_{4γ}` with
value `≠ (A−1)/(4γ)`). The retired statement also used the real-valued `decGf`, whose `sSup`
over `F = ℝ^A` returns the junk value `0` for zero-weight `q`, which made its first conjunct
true only through that junk value; the statement is therefore spelled out in `EReal`. -/
theorem igw_minimizes_dec_v2 {A : ℕ} (fhat : Fin A → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (piStar : (Fin A → ℝ) → Fin A) (hpiStar : ∀ f : Fin A → ℝ, ∀ π : Fin A, f π ≤ f (piStar f))
    (bstar : Fin A) (p : Fin A → ℝ) (hIGW : Contextual.IsIGW A fhat (2 * γ) bstar p) :
    (⨆ f : Fin A → ℝ,
        (((∑ π, p π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2)) : ℝ) : EReal))
        = ((((A : ℝ) - 1) / (4 * γ) : ℝ) : EReal) ∧
    (⨅ q : {q : Fin A → ℝ // (∀ π, 0 ≤ q π) ∧ ∑ π, q π = 1},
        ⨆ f : Fin A → ℝ,
          (((∑ π, q.1 π * (f (piStar f) - f π - γ * (f π - fhat π) ^ 2)) : ℝ) : EReal))
        = ((((A : ℝ) - 1) / (4 * γ) : ℝ) : EReal) := by sorry

end FoundationsRL.Structured
