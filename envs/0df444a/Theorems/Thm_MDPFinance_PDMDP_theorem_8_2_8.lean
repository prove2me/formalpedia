-- Prove2me | Theorems.Thm_MDPFinance_PDMDP_theorem_8_2_8
-- name    : MDPFinance.PDMDP.theorem_8_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:09:18.158245+00:00
-- url     : https://prove2.me/theorems/0386bbfe-2320-49b6-b13c-244392e58523
-- title:
--   Theorem 8.2.8 (Verification Theorem) — the Hamilton-Jacobi-Bellman equation
-- statement:
--   This is the classical continuous-time verification technique: if $v \in C^1(E) \cap IB_b$ solves the Hamilton-Jacobi-Bellman equation $\sup_{u\in U}\{Av(x,u)+r(x,u)\} = \beta v(x)$ (where $Av(x,u) := \mu(x,u)\cdot\nabla v(x) + \lambda\int(v(y)-v(x))\,Q(dy\mid x,u)$ is the process generator) and $f^*$ is a maximizer of the HJB equation defining a feedback state process $(X^*_t)$ via the closed-loop ODE $\dot x_t = \mu(x_t,f^*(x_t))$, then $v$ *is* the value function $V_\infty$ and the feedback policy $\pi^*_t := f^*(X^*_{t-})$ is optimal — provided the model has a bounding function with $\alpha_b<1$ and the bounding-function expectation vanishes in the limit for every policy. This is genuinely continuous-time content (a PDE-style verification argument), distinct in flavor from every other result in this chapter, which works through the discrete-time embedding.
--
--   **Formalization Note.** $E$ is specialized to a normed real vector space so that $\nabla v(x)$ typechecks as `fderiv ℝ v x`; the closed-loop control function $f$ solving Eq. (8.9)'s self-referential ODE is bundled as data satisfying its own defining self-consistency, matching this chunk's "data satisfying a defining formula" convention (Definition 8.1.1 only assumes existence/uniqueness of $\varphi^\alpha$ for a *given* $\alpha$, not of this self-referential closed-loop one, which the book introduces separately via Eq. (8.9) without re-deriving it).
--
--   **Moderation note.** The draft's verification theorem lacked the bounding function's `|r|` bound, the contraction `c_Q c_φ < 1`, the transversality condition `𝔼_x^π[e^{-βt} b(X_t)] → 0`, boundedness of the HJB supremum (so its real `⨆` was junk), measurability of `f^*`, and any link between `f^*` and the state process (its "closed-loop control" was a free function). Now all of these are hypotheses: `v ∈ C¹ ∩ IB_b` (derivative continuous), the HJB supremum bounded and equal to `β v(x)`, `f^*` a measurable maximizer, and `fclosed x` a control function solving the closed-loop equation `(fclosed x)(t) = f^*(φ_t^{fclosed x}(x))`. Conclusions: `J_∞ = v` and every realization of the stationary policy `fclosed` has value `v(x)`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 255, PDF 266, Theorem 8.2.8

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Model
import Definitions.Def_MDPFinance_PDMDP_Embedding
import Definitions.Def_MDPFinance_PDMDP_Bounding
import Definitions.Def_MDPFinance_PDMDP_Process

open MeasureTheory ProbabilityTheory Filter

namespace MDPFinance.PDMDP

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [MeasurableSpace U] [TopologicalSpace U] [OpensMeasurableSpace U]

/-- Theorem 8.2.8, the **Verification Theorem** (Bäuerle–Rieder, p. 255, PDF 266). Let a
Piecewise Deterministic Markov Decision Process be given with a bounding function `b`, `α_b < 1`
(`c_Q c_φ < 1`) and `𝔼^π_x[e^{-βt} b(X_t)] → 0` as `t → ∞` for all `π`, `x`. Suppose `v ∈ C¹(E)
∩ IB_b` solves the HJB equation `sup_{u∈U} {Av(x,u) + r(x,u)} = β v(x)` with `Av(x,u) :=
μ(x,u)·∇v(x) + λ ∫ (v(y)-v(x)) Q(dy|x,u)` (the supremum finite), and `f^*` is a maximizer of the
HJB equation which defines a state process through the closed-loop equation (8.9), `ẋ_t =
μ(x_t,f^*(x_t))` — the control function `fclosed x` with `(fclosed x)(t) = f^*(φ_t^{fclosed x}(x))`.
Then `v = V_∞` (read as `J_∞`, Theorem 8.2.1) and `π^*_t := f^*(X^*_{t-})` is an optimal Markov
policy: every realization of the stationary policy `fclosed` has value `v(x)`. -/
theorem theorem_8_2_8 (Mk : PDMDPModel E U) (Emb : EmbeddedKernel Mk) (b : E → ℝ)
    (cr cQ cφ : ℝ) (hb : IsBoundingFunctionPDMDP Mk b cr cQ cφ) (hαb : cQ * cφ < 1)
    (hconv : ∀ (f : ℕ → E → ControlFn U), IsPDPolicy f → ∀ (x : E) {Ω : Type*} [MeasurableSpace Ω]
        (R : PDMDPRealization Ω Mk f x),
        Tendsto (fun t => ∫⁻ ω, ENNReal.ofReal (Real.exp (-Mk.β * t) * b (R.X ω t)) ∂(R.ℙrob))
          atTop (nhds 0))
    (v : E → ℝ) (hv_diff : Differentiable ℝ v)
    (hv_diff_cont : Continuous fun x => fderiv ℝ v x) (hv_IBb : ∃ c, 0 ≤ c ∧ ∀ x, |v x| ≤ c * b x)
    (hHJB_bdd : ∀ x, BddAbove (Set.range fun u => fderiv ℝ v x (Mk.μ (x, u)) +
        Mk.lam * ∫ y, (v y - v x) ∂(Mk.Q (x, u)) + Mk.r (x, u)))
    (hHJB : ∀ x, (⨆ u, fderiv ℝ v x (Mk.μ (x, u)) + Mk.lam * ∫ y, (v y - v x) ∂(Mk.Q (x, u)) +
        Mk.r (x, u)) = Mk.β * v x)
    (fstar : E → U) (hfstar_meas : Measurable fstar)
    (hfstar_max : ∀ x, fderiv ℝ v x (Mk.μ (x, fstar x)) +
        Mk.lam * ∫ y, (v y - v x) ∂(Mk.Q (x, fstar x)) + Mk.r (x, fstar x) =
      ⨆ u, fderiv ℝ v x (Mk.μ (x, u)) + Mk.lam * ∫ y, (v y - v x) ∂(Mk.Q (x, u)) + Mk.r (x, u))
    (fclosed : E → ControlFn U) (hfclosed_meas : Measurable fclosed)
    (hfclosed : ∀ x t, 0 ≤ t → (fclosed x).1 t = fstar (Mk.φ t (fclosed x).1 x)) :
    (∀ x, JinfSup Mk Emb x = (v x : EReal)) ∧
      ∀ x {Ω : Type*} [MeasurableSpace Ω] (R : PDMDPRealization Ω Mk (fun _ => fclosed) x),
        R.Vpi = (v x : EReal) := by sorry

end MDPFinance.PDMDP
