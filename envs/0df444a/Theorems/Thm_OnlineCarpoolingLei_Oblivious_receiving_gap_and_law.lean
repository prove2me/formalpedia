-- Prove2me | Theorems.Thm_OnlineCarpoolingLei_Oblivious_receiving_gap_and_law
-- name    : OnlineCarpoolingLei.Oblivious.receiving_gap_and_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:49.507202+00:00
-- url     : https://prove2.me/theorems/d3dcea91-fd47-4e88-b331-38494ca0be87
-- title:
--   Proposition 3.4 — receiving gap at most $29$, $d_t\sim\mu_t$, and $\mathbb E e^{\langle\theta,d_t\rangle}\le e^{25\|\theta\|^2}$
-- statement:
--   Fix $n\ge2$, let the input $e_1,e_2,\dots$ be fixed in advance, and run the algorithm of Section 3.2 with independent $U_1,U_2,\dots$ uniform on $[0,1)$. Then:
--
--   1. every trajectory (every realization of the $U_t$ in $[0,1)$) has receiving gap at most $29$: $d_t(a_t)-d_t(b_t)\le29$ for all $t\ge1$;
--   2. for every $t\ge0$, $d_t$ has law $\mu_t$;
--   3. in particular, for all $t\ge0$ and $\theta\in\mathbb R^n$,
--   $$\mathbb E\,e^{\langle\theta,d_t\rangle}\le e^{25\|\theta\|^2}.$$
--
--   The two properties are (P1) and (P2) of the paper: the receiver is never far ahead of the sender after an update, and each $d_t$ is subgaussian with a constant parameter because its law is dominated in convex order by $N(0,50I_n)$. Theorem 1.2 combines them with the witness family of Lemma 4.2.
--
--   Differences from the source:
--   - encoding: vertex set $[n]$ and input $e_1,e_2,\dots$ → `Fin n` and `E : ℕ → Edge n` with `E t` $=e_{t+1}$ (likewise $U_{t+1}$ = `U t`); reason: relabelling and index shift
--   - encoding: "each trajectory" → every tape realization `u : ℕ → ℝ` with values in $[0,1)$; reason: the trajectories are exactly the runs on such realizations
--   - encoding: "$d_t$ has law $\mu_t$" → the pushforward of $P$ under $d_t$ equals `toMeasure (lawSeq E t)`, for every probability space carrying an independent uniform tape; reason: definition of law
--   - encoding: $\mathbb E e^{\langle\theta,d_t\rangle}$ → lower Lebesgue integral of `ENNReal.ofReal` of the positive integrand; reason: same value for a nonnegative integrand, no Bochner default
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Proposition 3.4, p.6 (PDF p.6); algorithm and (3.3) in Section 3.2, p.6

import Mathlib
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Model
import Definitions.Def_OnlineCarpoolingLei_Oblivious_ConvexOrder
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Algorithm

open MeasureTheory ProbabilityTheory

namespace OnlineCarpoolingLei.Oblivious

/-- Proposition 3.4 (p.6). Fix `n ≥ 2` and an input `e₁, e₂, …` in advance, and run the
algorithm of §3.2. Every trajectory (every realization of the tape in `[0,1)`) has receiving
gap at most `29`; for independent uniform `U₁, U₂, …` on `[0,1)`, `d_t` has law `μ_t`; and
`E e^{⟨θ, d_t⟩} ≤ e^{25 ‖θ‖²}` for all `t ≥ 0` and `θ ∈ ℝⁿ`. -/
theorem receiving_gap_and_law (n : ℕ) (hn : 2 ≤ n) (E : ℕ → Edge n) :
    (∀ u : ℕ → ℝ, (∀ t, u t ∈ Set.Ico (0 : ℝ) 1) →
      ∀ T : ℕ, GapAtMost E ((paperAlg n).signs E u) T 29) ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U : ℕ → Ω → ℝ), IsUniformTape P U →
      (∀ t : ℕ, P.map (fun ω => fun i => ((paperAlg n).disc E (fun s => U s ω) t i : ℝ)) =
          toMeasure (lawSeq E t)) ∧
      ∀ (t : ℕ) (θ : Fin n → ℝ),
        ∫⁻ ω, ENNReal.ofReal
            (Real.exp (ip θ (fun i => ((paperAlg n).disc E (fun s => U s ω) t i : ℝ)))) ∂P ≤
          ENNReal.ofReal (Real.exp (25 * sqNorm θ)) := by sorry

end OnlineCarpoolingLei.Oblivious
