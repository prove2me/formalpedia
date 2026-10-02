-- Prove2me | Theorems.Thm_MDPFinance_Contracting_theorem_7_3_5
-- name    : MDPFinance.Contracting.theorem_7_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:46:07.341795+00:00
-- url     : https://prove2.me/theorems/5bde60f1-2cc0-4603-a2ad-b9af642afca1
-- title:
--   Theorem 7.3.5 (Structure Theorem) — the contracting-model existence, uniqueness and rate theorem
-- statement:
--   This is the chapter's — and, per `triage.json`, the book's — central result. Under a bounding
--   function with $\beta\alpha_b < 1$ and one abstract structural hypothesis (a closed class $IM$
--   containing $0$, mapped into itself by $T$, on which maximizers always exist), it delivers, from
--   Banach's fixed point theorem alone, everything a numerical or theoretical treatment of an
--   infinite-horizon Markov Decision Process could want: value iteration converges to the true value
--   $J_\infty$ (a); $J_\infty$ is the *unique* fixed point of $T$ in $IM$ (b), and the smallest
--   $r$-superharmonic function there (c); value iteration converges at an explicit **geometric rate**
--   $\big(\frac{\beta\alpha_b}{1}\big)^n/(1-\beta\alpha_b)$ from *any* starting point $g \in IM$, not
--   merely qualitatively (d); and an optimal stationary policy exists, built from any maximizer of
--   $J_\infty$ (e). It is the direct, general-Borel-space generalization of what finite-state
--   dynamic-programming theorems (e.g. the platform's `BertsekasDP.discounted_main_theorem`,
--   `BertsekasDP.ssp_main_theorem`) establish only for finite state and action spaces: those proofs
--   work with a genuine metric space $\mathbb R^n$ and Banach's theorem on it directly, while this
--   theorem's content is that the *same* conclusion — including the *same* explicit convergence
--   rate — holds on an arbitrary Borel state space, the moment one abstract structural condition on
--   an abstract closed class $IM$ is checked.
--
--   **Formalization Note.** Part (d)'s explicit geometric rate is stated in full (not weakened to
--   qualitative convergence `T^ng → J_\infty`), since it is the fact that makes value iteration a
--   genuine numerical method with a computable error bound — this book's Theorem 7.5.12
--   (state-space discretization error, a different chunk) builds directly on it.
--
--   **Moderation note.** Part c) had the inequality reversed: it read "if $v\le Tv$ then $J_\infty\le v$", which is refutable (take $v\equiv-K$ with $K$ large in a bounded model: $v\le Tv$ but $J_\infty>v$). An $r$-superharmonic function is one with $v\ge Tv$, and the claim is that $J_\infty$ is the smallest such $v\in IM$; corrected.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 207, Theorem 7.3.5

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Contracting

/-- **Theorem 7.3.5 (Structure Theorem)** (Bäuerle–Rieder, p. 207, PDF 218, the goal theorem of
this mission). Let `b` be a bounding function and `\beta\alpha_b < 1`. If there exists a closed
subset `IM \subset IB_b` (closedness stated sequentially in the `\|\cdot\|_b`-norm, since no
pre-built `MetricSpace` instance for the weighted-sup-norm space is introduced in this mission)
and a set `\Delta \subset F` such that (i) `0 \in IM`, (ii) `T : IM \to IM` (via the real-valued
`T'`), (iii) for all `v \in IM`
there exists a maximizer `f \in \Delta` of `v`, then it holds: a) `J_\infty \in IM`, `J_\infty =
TJ_\infty` and `J_\infty = J` (Value Iteration). b) `J_\infty` is the unique fixed point of `T` in
`IM`. c) `J_\infty` is the smallest `r`-superharmonic function `v \in IM`, i.e. `J_\infty` is the
smallest function `v \in IM` with `v \ge Tv` (`r`-superharmonic: `Tv ≤ v`). d) Let `g \in IM`. Then `\|J_\infty - T^ng\|_b \le
\frac{(\beta\alpha_b)^n}{1-\beta\alpha_b}\|Tg-g\|_b`. e) There exists a maximizer `f \in \Delta`
of `J_\infty`, and every maximizer `f^*` of `J_\infty` defines an optimal stationary policy
`(f^*,f^*,\dots)`. `J_\infty` is identified with its real-valued representative in `IM \subset
IB_b` throughout (cast to `EReal` via the coercion where compared against `Jinf`/`Jlim`). -/
theorem theorem_7_3_5 {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] (M : MarkovDecisionModel E A)
    (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb) (hαb : M.β * αb < 1)
    (IMs : Set (E → ℝ)) (hIMsub : IMs ⊆ IBb b)
    (hIMclosed : ∀ (vn : ℕ → E → ℝ) (v : E → ℝ), (∀ n, vn n ∈ IMs) → v ∈ IBb b →
      Filter.Tendsto (fun n => normb b fun x => vn n x - v x) Filter.atTop (nhds 0) → v ∈ IMs)
    (Δ : Set (E → A))
    (h0 : (0 : E → ℝ) ∈ IMs) (hTmaps : ∀ v ∈ IMs, (fun x => T' M v x) ∈ IMs)
    (hmax : ∀ v ∈ IMs, ∃ f ∈ Δ, IsMaximizerOf M (fun x => (v x : EReal)) f) :
    (∃ v ∈ IMs, (∀ x, Jinf M x = (v x : EReal)) ∧ (∀ x, T' M v x = v x) ∧
        ∀ x, Jinf M x = Jlim M x) ∧
      (∀ v ∈ IMs, (∀ x, T' M v x = v x) → ∀ x, (v x : EReal) = Jinf M x) ∧
      (∀ v ∈ IMs, (∀ x, T' M v x ≤ v x) → ∀ x, Jinf M x ≤ (v x : EReal)) ∧
      (∀ g ∈ IMs, ∀ n : ℕ,
        normb b (fun x => (Jinf M x).toReal - (T' M)^[n] g x) ≤
          (M.β * αb) ^ n / (1 - M.β * αb) * normb b (fun x => T' M g x - g x)) ∧
      ((∃ f ∈ Δ, IsMaximizerOf M (Jinf M) f) ∧
        ∀ fstar : E → A, IsMaximizerOf M (Jinf M) fstar →
          ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) := by sorry

end MDPFinance.Contracting
