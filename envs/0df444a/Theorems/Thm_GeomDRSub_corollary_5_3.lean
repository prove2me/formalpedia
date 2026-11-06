-- Prove2me | Theorems.Thm_GeomDRSub_corollary_5_3
-- name    : GeomDRSub.corollary_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:18:44.772625+00:00
-- url     : https://prove2.me/theorems/b4ce0270-1021-42bc-ab1c-4d5583216eaa
-- title:
--   Corollary 5.3 — Algorithm 1 attains $\alpha(\zeta)$-regret $O(\sqrt T)$ with one gradient query per round
-- statement:
--   Let $\zeta\in[0,1]$, let $K\subseteq[0,1]^d$ be nonempty, compact, convex and down-closed with $\zeta\mathbf 1\in K$, let $D\ge\operatorname{diam}K$, and let $f_1,\dots,f_T$ be nonnegative continuously differentiable DR-submodular functions on the cube, fixed by an oblivious adversary. Run Algorithm 1 (OMBQ with one gradient query and one projection per round): $x_1=\mathbf 0$, play $p_t=h_\zeta(x_t)$, draw $I_t,S_t,Y_t$ as in (49), query $V_t(Y_t)$, set $\hat g_t=d[V_t(Y_t)]_{I_t}e_{I_t}$ and $x_{t+1}=\Pi_K(x_t+\eta\hat g_t)$ with $\eta=D/\sqrt{TV_{\mathrm{gen}}}$ (and $\eta=0$ if $D=0$ or $V_{\mathrm{gen}}=0$). Then for every comparator $o\in K$ the expected $\alpha(\zeta)$-regret
--   $$
--   \mathrm{Reg}_{\alpha(\zeta)}(T)=\alpha(\zeta)\sum_{t=1}^Tf_t(o)-\mathbb E\sum_{t=1}^Tf_t(p_t)
--   $$
--   satisfies
--   $$
--   \mathrm{Reg}_{\alpha(\zeta)}(T)\le\begin{cases}\alpha(\zeta)DB\sqrt{2dT},&\text{exact gradients, }\|\nabla f_t\|_2\le B,\ V_{\mathrm{gen}}=2dB^2,\\ \alpha(\zeta)DdB_1\sqrt T,&\text{stochastic gradients with (6)},\ V_{\mathrm{gen}}=d^2B_1^2,\\ \alpha(\zeta)D\sqrt{(2dB^2+d^2\sigma_g^2)T},&\text{stochastic gradients with (7)}.\end{cases}
--   $$
--   Under (6) and (7), with $V_{\mathrm{gen}}=\min\{d^2B_1^2,\,2dB^2+d^2\sigma_g^2\}$, the second and third bounds both hold; and for unbiased responses with (7) and $V_{\mathrm{gen}}=2dB^2+d^2\sigma_g^2$ the third bound holds. The oracle conditions (6)–(7) are conditional on the history and the current round's draws.
--
--   This is the paper's first main result: one gradient query per round achieves the geometry-dependent coefficient $\alpha(\zeta)$, which is $4/9$ for $\zeta=0$ and $1/2$ once $\zeta\ge1/2$, with $O(\sqrt T)$ regret.
--
--   **Formalization Note** The run of Algorithm 1 is a family of random variables on an arbitrary probability space, with independent uniform draws (the branch of $Y_t$ through a uniform coin) and the projection update for every outcome.
--
--   Differences from the source:
--   - reading: (6)/(7) conditional on F (objective sequence, current query point, preceding choices and responses) → conditional on R.info t (history before round t plus this round's draws); reason: the smallest F the page allows; conditions relative to a larger F imply these (tower property), so this is the strongest reading
--   - reading: case "stochastic gradients with (7)" and "Under (7), the second and third bounds both hold when V_gen is the minimum in (50)" → conjunct 3: (6) and (7) with V_gen = min{d²B₁², 2dB² + d²σ_g²}, concluding both the second and third bounds; reason: the sentence after (66) and the third case of (50)
--   - generalization: the three cases of (66) → conjunct 4: unbiased responses with (7) and V_gen = 2dB² + d²σ_g², third bound; reason: covers the other reading of "stochastic gradients with (7)" (for which p.9 notes that (6) holds with B₁² = B² + σ_g²); conjuncts 1–3 state (66) as on the page
--   - reading: "Algorithm 1 uses one gradient query and one projection per round" → no separate conjunct; a run has one response V_t and one projection step per round by construction; reason: a remark on the procedure, which the definition of a run carries
--   - encoding: Reg_α(T) = α max_{o∈K} Σ f_t(o) − E Σ f_t(p_t) → the bound for every o ∈ K; reason: equal, since K is compact and Σ f_t continuous (p.9)
--   - encoding: Algorithm 1 with D > 0, V_gen > 0; the fixed state if D = 0 or V_gen = 0 → step stepSize D V_gen T; reason: D/√(TV_gen), or 0 which holds the state at x₁
--   - encoding: branch probabilities 1 − p_I, p_I; rounds 1..T; coordinates [d] → uniform coin U_t; rounds 0..T−1; Fin d; reason: same laws and indices; a page run with Bernoulli branches yields such U_t on an extension of the space (draw U_t given the branch, independently of everything else), and (6)/(7) given the branches then hold given U_t
--   - encoding: ℝ^d with coordinatewise order; C¹ on [0,1]^d with boundary gradients → EuclideanSpace ℝ (Fin d), order written out; ContDiffOn ℝ 1 on cube d with fderivWithin; reason: Lean conventions; same objects
--   - encoding: finite conditional moments in (6)/(7); bound B₁ → integrability of V_t, ‖V_t‖², ‖V_t − ∇f_t(Y_t)‖²; 0 ≤ B₁; reason: presupposed by the conditional expectations (Lean's junk value 0 otherwise); B₁ bounds a norm
--   - encoding: value bound 0 ≤ f_t ≤ M of (5), and the gradient bound B of (5) in the case of (6) alone → nonnegativity only, and no B in conjunct 2; reason: neither appears in that conclusion, and C¹ functions on the compact cube have both bounds
--   - encoding: I_t uniform on [d] → uniform law on Fin d, the zero measure at d = 0; reason: the draw is undefined at d = 0; a value of Fin 0 cannot exist on a nonempty Ω, so no run exists there
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Corollary 5.3, p.21, Eq. (66); Algorithm 1, p.20

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_IsAdmissible
import Definitions.Def_GeomDRSub_gradQ
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_GeomDRSub_alphaLow
import Definitions.Def_GeomDRSub_hAct
import Definitions.Def_GeomDRSub_stepSize
import Definitions.Def_GeomDRSub_Alg1Run
import Definitions.Def_GeomDRSub_Alg1Run_Y
import Definitions.Def_GeomDRSub_IsAlg1Run
import Definitions.Def_GeomDRSub_OracleUnbiased
import Definitions.Def_GeomDRSub_OracleMoment
import Definitions.Def_GeomDRSub_OracleNoise

namespace GeomDRSub

open MeasureTheory ProbabilityTheory

/-- **Corollary 5.3 (general first-order guarantee).** Aggarwal–Lu, arXiv:2610.00545, p.21:
"Algorithm 1 uses one gradient query and one projection per round. Its expected regret satisfies
`Reg_{α(ζ)}(T) ≤ α(ζ)DB√(2dT)` (exact gradients), `α(ζ)DdB₁√T` (stochastic gradients with (6)),
`α(ζ)D√((2dB² + d²σ_g²)T)` (stochastic gradients with (7)). (66) Under (7), the second and third
bounds both hold when `V_gen` is the minimum in (50) of Lemma 5.1." After the proof: "If `D = 0` or
`V_gen = 0`, Lemma 5.2 with a fixed state gives zero linear regret and the same bound."

Setting: `K` admissible with diagonal level `ζ ∈ [0,1]` (p.8), `D ≥ diam K`, any horizon `T`, and
objectives `f_t` (fixed before any randomness: oblivious adversary) that are nonnegative and
DR-submodular on the cube. A run of Algorithm 1 (`IsAlg1Run`, with the step size `η = D/√(T V_gen)`,
or `0` in the degenerate case) plays `p_t = h_ζ(x_t)`. The regret
`Reg_α(T) = α max_{o∈K} ∑_t f_t(o) − E ∑_t f_t(p_t)` is bounded for every comparator `o ∈ K`.

Conjuncts:
1. exact gradients, `V_gen = 2dB²`: `Reg ≤ α(ζ)DB√(2dT)`;
2. (6), `V_gen = d²B₁²`: `Reg ≤ α(ζ)DdB₁√T`;
3. (6) and (7), `V_gen = min{d²B₁², 2dB² + d²σ_g²}`: both `Reg ≤ α(ζ)DdB₁√T` and
   `Reg ≤ α(ζ)D√((2dB² + d²σ_g²)T)`;
4. unbiasedness of (6) and (7), `V_gen = 2dB² + d²σ_g²`: `Reg ≤ α(ζ)D√((2dB² + d²σ_g²)T)`.

**Formalization Note.** Rounds and coordinates are 0-based; the branch of `Y_t` is chosen by a
uniform coin `U_t`. The oracle conditions are relative to `R.info t` (history plus this round's
draws), the strongest reading of the page's `F`. The value bound `M` of (5) is not assumed: no
conclusion uses it. For `d = 0` there is no coordinate to draw: `I t ω : Fin 0` is impossible on a
nonempty `Ω`, so no run exists. -/
theorem corollary_5_3 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ζ : ℝ) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : IsAdmissible K ζ) (D : ℝ) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D) (T : ℕ)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ∀ t < T, (∀ y ∈ cube d, 0 ≤ f t y) ∧ IsDRSubmodular (f t)) :
    -- (a) exact gradients, V_gen = 2dB²
    (∀ (B : ℝ) (R : Alg1Run d Ω), (∀ t < T, ∀ y ∈ cube d, ‖gradQ (f t) y‖ ≤ B) →
      IsAlg1Run P K (stepSize D (2 * d * B ^ 2) T) T R →
      (∀ t < T, ∀ ω, R.V t ω = gradQ (f t) (R.Y ζ t ω)) →
      ∀ o ∈ K, alphaLow ζ * ∑ t ∈ Finset.range T, f t o -
          ∫ ω, ∑ t ∈ Finset.range T, f t (hAct ζ (R.x t ω)) ∂P ≤
        alphaLow ζ * D * B * Real.sqrt (2 * d * T)) ∧
    -- (b) stochastic gradients with (6), V_gen = d²B₁²
    (∀ (B₁ : ℝ) (R : Alg1Run d Ω), 0 ≤ B₁ →
      IsAlg1Run P K (stepSize D (d ^ 2 * B₁ ^ 2) T) T R →
      OracleUnbiased P f ζ T R → OracleMoment P T B₁ R →
      ∀ o ∈ K, alphaLow ζ * ∑ t ∈ Finset.range T, f t o -
          ∫ ω, ∑ t ∈ Finset.range T, f t (hAct ζ (R.x t ω)) ∂P ≤
        alphaLow ζ * D * d * B₁ * Real.sqrt T) ∧
    -- (c) stochastic gradients with (6) and (7), V_gen = min{d²B₁², 2dB² + d²σ_g²}: both bounds
    (∀ (B B₁ σg : ℝ) (R : Alg1Run d Ω), 0 ≤ B₁ → (∀ t < T, ∀ y ∈ cube d, ‖gradQ (f t) y‖ ≤ B) →
      IsAlg1Run P K (stepSize D (min (d ^ 2 * B₁ ^ 2) (2 * d * B ^ 2 + d ^ 2 * σg ^ 2)) T) T R →
      OracleUnbiased P f ζ T R → OracleMoment P T B₁ R → OracleNoise P f ζ T σg R →
      ∀ o ∈ K,
        (alphaLow ζ * ∑ t ∈ Finset.range T, f t o -
            ∫ ω, ∑ t ∈ Finset.range T, f t (hAct ζ (R.x t ω)) ∂P ≤
          alphaLow ζ * D * d * B₁ * Real.sqrt T) ∧
        (alphaLow ζ * ∑ t ∈ Finset.range T, f t o -
            ∫ ω, ∑ t ∈ Finset.range T, f t (hAct ζ (R.x t ω)) ∂P ≤
          alphaLow ζ * D * Real.sqrt ((2 * d * B ^ 2 + d ^ 2 * σg ^ 2) * T))) ∧
    -- (d) unbiased stochastic gradients with (7), V_gen = 2dB² + d²σ_g²
    (∀ (B σg : ℝ) (R : Alg1Run d Ω), (∀ t < T, ∀ y ∈ cube d, ‖gradQ (f t) y‖ ≤ B) →
      IsAlg1Run P K (stepSize D (2 * d * B ^ 2 + d ^ 2 * σg ^ 2) T) T R →
      OracleUnbiased P f ζ T R → OracleNoise P f ζ T σg R →
      ∀ o ∈ K, alphaLow ζ * ∑ t ∈ Finset.range T, f t o -
          ∫ ω, ∑ t ∈ Finset.range T, f t (hAct ζ (R.x t ω)) ∂P ≤
        alphaLow ζ * D * Real.sqrt ((2 * d * B ^ 2 + d ^ 2 * σg ^ 2) * T)) := by sorry

end GeomDRSub
