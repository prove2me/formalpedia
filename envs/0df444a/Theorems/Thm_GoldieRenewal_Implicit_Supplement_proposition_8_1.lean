-- Prove2me | Theorems.Thm_GoldieRenewal_Implicit_Supplement_proposition_8_1
-- name    : GoldieRenewal.Implicit.Supplement.proposition_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:17:51.44631+00:00
-- url     : https://prove2.me/theorems/5b97941e-ddbb-4581-890b-f495ab8ed874
-- title:
--   Proposition 8.1 (corrected: E log⁺ Q < ∞) — finite backward limit and unique law on [0, ∞) solving (8.1)
-- statement:
--   Suppose $M\ge0$, $N\ge0$, $Q>0$ a.s., and that $(Q,N,M)$, $(Q',N',M')$, $((Q_n,N_n,M_n))_{n\ge1}$ are i.i.d. Set $\Xi_n(t):=M_nt+N_n\sqrt t+Q_n$ for $t\ge0$. If
--   $$
--   E\log^+N<\infty\quad(8.2)\qquad\text{and}\qquad -\infty\le E\log\Bigl(M+\frac N{2\sqrt{Q'}}\Bigr)<0\quad(8.3),
--   $$
--   and additionally $E\log^+Q<\infty$, then $\tilde S:=\lim_{n\to\infty}\Xi_1\circ\Xi_2\circ\cdots\circ\Xi_n(t)$ exists and is finite almost surely, and its law is the unique law on $[0,\infty)$ satisfying (8.1),
--   $$
--   S\overset{L}{=}MS+N\sqrt S+Q,\qquad S\text{ independent of }(Q,N,M).
--   $$
--
--   Equation (8.1) is the square $S=R^2$ of the random polynomial equation (1.7); Theorems 8.2 and 8.3 concern the law found here.
--
--   **Formalization Note** The conclusion supplies one real random variable $S$ with $\Xi_1\circ\cdots\circ\Xi_n(t)\to S$ a.s. for every $t\ge0$ (the limit does not depend on $t$). (8.3) concerns the law of $M+N/(2\sqrt{Q'})$ with $Q'$ independent of $(M,N)$; its $E\log$ is computed in $\overline{\mathbb R}$ with $\log0=-\infty$, and "$-\infty\le E\log<0$" is $E\log^+<\infty$ together with $E\log<0$. A law on $[0,\infty)$ satisfying (8.1) is a probability measure with no mass on $(-\infty,0)$ fixed by the law operator of (8.1).
--
--   **Source correction** The printed proposition is false without control of the positive logarithmic moment of $Q$. The domination argument on p. 161 invokes Proposition 6.1, which requires $E\log(1\vee Q)<\infty$. This condition is added here. It is automatic under the positive moment assumptions in Theorems 8.2 and 8.3. See `DISPROOF.md` for the explicit divergent example.
--
--   Differences from the source:
--
--   - correction: Proposition 8.1 assumes (8.2) and (8.3), with no moment condition on Q → also E log⁺ Q < ∞; reason: the comparison on p. 161 with Proposition 6.1 requires E log(1 ∨ Q) < ∞; without it, M = 1/2, N = 0, Q = 2^K with P(K = k) = 1/(k(k+1)) has divergent backward iterates despite all printed assumptions; Q > 0 makes log⁺ Q = log(1 ∨ Q)
--   - correction: the first coefficient tuple in Proposition 8.1 is printed (Q, M) → (Q, N, M); reason: the other coefficient tuples and Ξ_n contain N; the i.i.d. assumption concerns triples
--   - encoding: S̃ := lim Ξ₁ ∘ ⋯ ∘ Ξ_n(t) exists and is finite a.s. (for any t ≥ 0) → there is a real S with Ξ₁ ∘ ⋯ ∘ Ξ_n(t) → S a.s. for every t ≥ 0; reason: the limit is the same for every t (proof, p. 162); real-valued means finite
--   - encoding: −∞ ≤ E log(M + N/(2√Q′)) < 0, with Q′ an independent copy of Q → E log⁺ < ∞ and E log < 0 in EReal for the image of law(Q, N, M) ⊗ law(Q) under m + n/(2√q′); reason: the expectation is determined by that product law; E log < 0 is only meaningful when E log⁺ < ∞
--   - encoding: its law is the unique law on [0, ∞) satisfying (8.1) → the law of S has no mass on (−∞, 0), is fixed by the law operator of (8.1), and every such fixed probability law on [0, ∞) equals it; reason: the operator encodes S independent of (Q, N, M)
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 142, Proposition 8.1; proof pp. 161–162

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_Supplement_Letac
import Definitions.Def_GoldieRenewal_Implicit_Supplement_Models

namespace GoldieRenewal.Implicit.Supplement

open MeasureTheory ProbabilityTheory Filter Topology

/-- **Proposition 8.1, corrected** (Goldie, *Implicit renewal theory and tails of solutions of random
equations*, Ann. Appl. Probab. 1(1) (1991), p. 142). Suppose `M ≥ 0`, `N ≥ 0`, `Q > 0` a.s. and
that `(Q, N, M)`, `(Q′, N′, M′)`, `((Q_n, N_n, M_n))_{n≥1}` are i.i.d. Set
`Ξ_n(t) := M_n t + N_n √t + Q_n` for `t ≥ 0`. If (8.2) `E log⁺ N < ∞` and (8.3)
`−∞ ≤ E log(M + N/(2√Q′)) < 0`, and additionally `E log⁺ Q < ∞`, then `S̃ := lim_{n→∞} Ξ₁ ∘ Ξ₂ ∘ ⋯ ∘ Ξ_n(t)` exists and is finite,
almost surely, and its law is the unique law on `[0, ∞)` satisfying (8.1) `S =_L MS + N√S + Q`,
`S` independent of `(Q, N, M)`.

**Formalization Note** `μ` is the law of `(Q, N, M)` (`p.1 = Q`, `p.2.1 = N`, `p.2.2 = M`); the
sequence is stored 0-based. `S̃` does not depend on `t`: the conclusion provides one real `S` with
`Ξ₁ ∘ ⋯ ∘ Ξ_n(t) → S` a.s. for every `t ≥ 0`. `S` is an a.e. limit of measurable maps, so `P.map S`
is its law. (8.3) concerns `M + N/(2√Q′)` with `Q′` an independent copy of `Q` (`coeffLaw83 μ`);
its `E log` is `logAbsMean` (in `EReal`, `log 0 = −∞`), and "`−∞ ≤ E log < 0`" is `E log⁺ < ∞` and
`E log < 0`. (8.2) is `logPlusMoment` of the law of `N`. A law "on `[0, ∞)` satisfying (8.1)" is a
probability measure `ρ` with `ρ(−∞, 0) = 0` fixed by `polyOperator μ`.

**Source correction** The printed assumptions omit `E log⁺ Q < ∞`. This is needed by the
comparison with Proposition 6.1 on p. 161. With `M = 1/2`, `N = 0` and `Q = 2^K`, where
`P(K = k) = 1/(k(k+1))` for `k ≥ 1`, all printed assumptions hold but the backward iterates
diverge almost surely. The added hypothesis excludes this infinite-log-moment obstruction;
it is already implied by the positive moment of `Q` in Theorems 8.2 and 8.3. The printed
first coefficient tuple `(Q, M)` is read `(Q, N, M)`, as the remaining tuples and maps require. -/
theorem proposition_8_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (ℝ × ℝ × ℝ)) [IsProbabilityMeasure μ]
    (QNM : ℕ → Ω → ℝ × ℝ × ℝ) (hQNM : ∀ i, Measurable (QNM i))
    (hQNM_indep : iIndepFun QNM P) (hQNM_law : ∀ i, P.map (QNM i) = μ)
    (hM_nonneg : μ {p | p.2.2 < 0} = 0) (hN_nonneg : μ {p | p.2.1 < 0} = 0)
    (hQ_pos : μ {p | p.1 ≤ 0} = 0)
    (h_8_2 : GoldieRenewal.Implicit.logPlusMoment (μ.map (fun p => p.2.1)) < ⊤)
    (hlogQ : GoldieRenewal.Implicit.logPlusMoment (μ.map Prod.fst) < ⊤)
    (h_8_3_plus : GoldieRenewal.Implicit.logPlusMoment (coeffLaw83 μ) < ⊤)
    (h_8_3 : GoldieRenewal.Implicit.logAbsMean (coeffLaw83 μ) < 0) :
    ∃ S : Ω → ℝ,
      (∀ t : ℝ, 0 ≤ t →
        ∀ᵐ ω ∂P, Tendsto (fun n => backwardIter (xiMap QNM) n t ω) atTop (𝓝 (S ω))) ∧
      (P.map S) (Set.Iio 0) = 0 ∧
      polyOperator μ (P.map S) = P.map S ∧
      ∀ ρ : ProbabilityMeasure ℝ, (ρ : Measure ℝ) (Set.Iio 0) = 0 →
        polyOperator μ (ρ : Measure ℝ) = ρ → (ρ : Measure ℝ) = P.map S := by sorry

end GoldieRenewal.Implicit.Supplement
