-- Prove2me | Theorems.Thm_GeomDRSub_lemma_5_1
-- name    : GeomDRSub.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:29.3192+00:00
-- url     : https://prove2.me/theorems/c92fc5dc-b535-4f82-aa6b-f0c175471f4f
-- title:
--   Lemma 5.1 — unbiased one-gradient query with second-moment bound $V_{\mathrm{gen}}$
-- statement:
--   Let $\zeta\in[0,1]$, let $f$ be a nonnegative continuously differentiable DR-submodular function on the cube, and let $x\in[0,1]^d$ be a state with $p=h_\zeta(x)$. On a probability space, draw $I$ uniformly from $[d]$, $S$ uniformly from $[0,1]$ and the branch of the query point $Y$ as in (49) ($Y=\ell_{I,S}$ with probability $1-p_I$, $Y=u_{I,S}$ with probability $p_I$); let $V$ be the gradient response at $Y$ and $\hat g=d\,[V]_Ie_I$. Then $\mathbb E\hat g=g_\zeta(f,x)$ and $\mathbb E\|\hat g\|_2^2\le V_{\mathrm{gen}}$, where
--   $$
--   V_{\mathrm{gen}}=\begin{cases}2dB^2,&\text{exact gradients }V=\nabla f(Y),\ \|\nabla f\|_2\le B\text{ on the cube},\\ d^2B_1^2,&\text{stochastic gradients satisfying (6)},\\ \min\{d^2B_1^2,\ 2dB^2+d^2\sigma_g^2\},&\text{stochastic gradients satisfying (6) and (7)},\end{cases}
--   $$
--   and also $V_{\mathrm{gen}}=2dB^2+d^2\sigma_g^2$ for unbiased responses satisfying (7). Here (6) is $\mathbb E[V\mid I,S,U]=\nabla f(Y)$ and $\mathbb E[\|V\|_2^2\mid I,S,U]\le B_1^2$, and (7) is $\mathbb E[\|V-\nabla f(Y)\|_2^2\mid I,S,U]\le\sigma_g^2$.
--
--   The estimate uses one gradient response per round; it is the field estimate of Algorithm 1.
--
--   Differences from the source:
--   - generalization: state x ∈ K → state x ∈ [0,1]^d; reason: K ⊆ [0,1]^d and the proof uses only that x lies in the cube; specializes to x ∈ K
--   - generalization: three cases of (50) → a fourth conjunct: unbiased responses with (7) only give E‖ĝ‖² ≤ 2dB² + d²σ_g²; reason: the derivation (57)–(58) uses only the first condition of (6) and (7); the three cases of (50) are stated as on the page
--   - reading: conditional on f and x, (6)/(7) given F (objective, query point, preceding choices) → f and x deterministic; (6)/(7) given σ(I, S, U); reason: σ(I, S, U) determines the query point and is the smallest such F, so this is the strongest reading
--   - reading: the cost sentence (one gradient response, O(d log d) and O(d) arithmetic) → not formalized beyond ĝ using one response V; reason: operation counts are a remark on the procedure; the Lean states the probabilistic content
--   - encoding: branch probabilities 1 − p_I and p_I → a uniform coin U with Y = u_{I,S} iff U < p_I; reason: same conditional law; a page draw with a Bernoulli branch yields such a U on an extension of the space (draw U given the branch, independently of everything else), and (6)/(7) given the branch then hold given U
--   - encoding: finite conditional moments → integrability of V, ‖V‖², ‖V − ∇f(Y)‖²; reason: presupposed by the conditional expectations (Lean's junk value 0 otherwise)
--   - encoding: I uniform on [d] → law drawLaw d, which is the zero measure at d = 0; reason: the draw is undefined at d = 0; the hypotheses then cannot hold
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Lemma 5.1, p.18, Eq. (50); setting Eq. (49), p.17

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_gradQ
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_GeomDRSub_field
import Definitions.Def_GeomDRSub_queryPt
import Definitions.Def_GeomDRSub_gHat
import Definitions.Def_GeomDRSub_drawLaw

namespace GeomDRSub

open MeasureTheory ProbabilityTheory

/-- **Lemma 5.1 (unbiased one-gradient query).** Aggarwal–Lu, arXiv:2610.00545, p.18: "Conditional
on the current objective `f` and state `x`, the estimate `ĝ` in (49) obeys `Eĝ = g_ζ(f, x)`,
`E‖ĝ‖₂² ≤ V_gen`, where `V_gen := 2dB²` (exact gradients), `d²B₁²` (stochastic gradients
satisfying (6)), `min{d²B₁², 2dB² + d²σ_g²}` (stochastic gradients satisfying (6) and (7)). (50)
The field estimate requires one gradient response, O(d log d) arithmetic for the order, and O(d)
arithmetic to form the query point."

Setting (49), p.17: for a state `x`, draw `I` uniform on `[d]`, `S` uniform on `[0,1]`, take
`Y = u_{I,S}` with probability `p_I` and `ℓ_{I,S}` otherwise (here through a uniform coin `U`), query
the gradient response `V = V(Y)`, and set `ĝ = d [V]_I e_I`.

One round on a probability space `(Ω, P)`: `(I, S, U)` has law `drawLaw d`, and `V` is the
response. Conjuncts:
1. exact gradients (`V = ∇f(Y)`, `‖∇f‖ ≤ B` on the cube): `Eĝ = g_ζ(f, x)`, `E‖ĝ‖² ≤ 2dB²`;
2. (6) given `σ(I, S, U)`: `Eĝ = g_ζ(f, x)`, `E‖ĝ‖² ≤ d²B₁²`;
3. (6) and (7), with `‖∇f‖ ≤ B`: `Eĝ = g_ζ(f, x)`, `E‖ĝ‖² ≤ min{d²B₁², 2dB² + d²σ_g²}`;
4. unbiasedness of (6) and (7), with `‖∇f‖ ≤ B`: `Eĝ = g_ζ(f, x)`, `E‖ĝ‖² ≤ 2dB² + d²σ_g²`.

**Formalization Note.** The state `x` is any point of the cube (the page has `x ∈ K ⊆ [0,1]^d`).
The oracle conditions are taken given `σ(I, S, U)`, which determines the query point `Y`; the
objective and the state are deterministic here. Their integrability clauses are what the
conditional expectations presuppose. The operation counts of the last sentence describe the
procedure and are not formalized. -/
theorem lemma_5_1 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ζ : ℝ) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf0 : ∀ y ∈ cube d, 0 ≤ f y) (hf : IsDRSubmodular f)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ cube d)
    (I : Ω → Fin d) (S U : Ω → ℝ) (hISU : Measurable (fun ω => (I ω, S ω, U ω)))
    (hlaw : P.map (fun ω => (I ω, S ω, U ω)) = drawLaw d)
    (V : Ω → EuclideanSpace ℝ (Fin d)) (hV : Measurable V) :
    -- exact gradients
    (∀ B : ℝ, (∀ y ∈ cube d, ‖gradQ f y‖ ≤ B) →
      (∀ ω, V ω = gradQ f (queryPt ζ x (I ω) (S ω) (U ω))) →
      ∫ ω, gHat (I ω) (V ω) ∂P = field ζ f x ∧
        ∫ ω, ‖gHat (I ω) (V ω)‖ ^ 2 ∂P ≤ 2 * d * B ^ 2) ∧
    -- stochastic gradients satisfying (6)
    (∀ B₁ : ℝ, Integrable V P → Integrable (fun ω => ‖V ω‖ ^ 2) P →
      P[V | MeasurableSpace.comap (fun ω => (I ω, S ω, U ω)) inferInstance] =ᵐ[P]
        (fun ω => gradQ f (queryPt ζ x (I ω) (S ω) (U ω))) →
      P[fun ω => ‖V ω‖ ^ 2 | MeasurableSpace.comap (fun ω => (I ω, S ω, U ω)) inferInstance]
        ≤ᵐ[P] (fun _ => B₁ ^ 2) →
      ∫ ω, gHat (I ω) (V ω) ∂P = field ζ f x ∧
        ∫ ω, ‖gHat (I ω) (V ω)‖ ^ 2 ∂P ≤ d ^ 2 * B₁ ^ 2) ∧
    -- stochastic gradients satisfying (6) and (7)
    (∀ B B₁ σg : ℝ, (∀ y ∈ cube d, ‖gradQ f y‖ ≤ B) →
      Integrable V P → Integrable (fun ω => ‖V ω‖ ^ 2) P →
      Integrable (fun ω => ‖V ω - gradQ f (queryPt ζ x (I ω) (S ω) (U ω))‖ ^ 2) P →
      P[V | MeasurableSpace.comap (fun ω => (I ω, S ω, U ω)) inferInstance] =ᵐ[P]
        (fun ω => gradQ f (queryPt ζ x (I ω) (S ω) (U ω))) →
      P[fun ω => ‖V ω‖ ^ 2 | MeasurableSpace.comap (fun ω => (I ω, S ω, U ω)) inferInstance]
        ≤ᵐ[P] (fun _ => B₁ ^ 2) →
      P[fun ω => ‖V ω - gradQ f (queryPt ζ x (I ω) (S ω) (U ω))‖ ^ 2 |
          MeasurableSpace.comap (fun ω => (I ω, S ω, U ω)) inferInstance] ≤ᵐ[P] (fun _ => σg ^ 2) →
      ∫ ω, gHat (I ω) (V ω) ∂P = field ζ f x ∧
        ∫ ω, ‖gHat (I ω) (V ω)‖ ^ 2 ∂P ≤ min (d ^ 2 * B₁ ^ 2) (2 * d * B ^ 2 + d ^ 2 * σg ^ 2)) ∧
    -- unbiased stochastic gradients satisfying (7)
    (∀ B σg : ℝ, (∀ y ∈ cube d, ‖gradQ f y‖ ≤ B) → Integrable V P →
      Integrable (fun ω => ‖V ω - gradQ f (queryPt ζ x (I ω) (S ω) (U ω))‖ ^ 2) P →
      P[V | MeasurableSpace.comap (fun ω => (I ω, S ω, U ω)) inferInstance] =ᵐ[P]
        (fun ω => gradQ f (queryPt ζ x (I ω) (S ω) (U ω))) →
      P[fun ω => ‖V ω - gradQ f (queryPt ζ x (I ω) (S ω) (U ω))‖ ^ 2 |
          MeasurableSpace.comap (fun ω => (I ω, S ω, U ω)) inferInstance] ≤ᵐ[P] (fun _ => σg ^ 2) →
      ∫ ω, gHat (I ω) (V ω) ∂P = field ζ f x ∧
        ∫ ω, ‖gHat (I ω) (V ω)‖ ^ 2 ∂P ≤ 2 * d * B ^ 2 + d ^ 2 * σg ^ 2) := by sorry

end GeomDRSub
